// /Copyright 2003-2005 Arthur van Hoff, Rick Blair
// Licensed under Apache License version 2.0
// Original license LGPL

package javax.jmdns.impl;

import java.io.IOException;
import java.net.DatagramPacket;
import java.net.Inet4Address;
import java.net.Inet6Address;
import java.net.InetAddress;
import java.net.MulticastSocket;
import java.net.SocketException;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.locks.ReentrantLock;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.jmdns.JmDNS;
import javax.jmdns.ServiceEvent;
import javax.jmdns.ServiceInfo;
import javax.jmdns.ServiceInfo.Fields;
import javax.jmdns.ServiceListener;
import javax.jmdns.ServiceTypeListener;
import javax.jmdns.impl.ListenerStatus.ServiceListenerStatus;
import javax.jmdns.impl.ListenerStatus.ServiceTypeListenerStatus;
import javax.jmdns.impl.constants.DNSConstants;
import javax.jmdns.impl.constants.DNSRecordClass;
import javax.jmdns.impl.constants.DNSRecordType;
import javax.jmdns.impl.constants.DNSState;
import javax.jmdns.impl.tasks.DNSTask;

// REMIND: multiple IP addresses

/**
 * mDNS implementation in Java.
 * 
 * @author Arthur van Hoff, Rick Blair, Jeff Sonstein, Werner Randelshofer, Pierre Frisch, Scott Lewis
 */
public class JmDNSImpl extends JmDNS implements DNSStatefulObject, DNSTaskStarter {
    private static Logger logger = Logger.getLogger(JmDNSImpl.class.getName());

    public enum Operation {
        Remove, Update, Add, RegisterServiceType, Noop
    }

    /**
     * This is the multicast group, we are listening to for multicast DNS messages.
     */
    private volatile InetAddress                                     _group;
    /**
     * This is our multicast socket.
     */
    private volatile MulticastSocket                                 _socket;

    /**
     * Holds instances of JmDNS.DNSListener. Must by a synchronized collection, because it is updated from concurrent threads.
     */
    private final List<DNSListener>                                  _listeners;

    /**
     * Holds instances of ServiceListener's. Keys are Strings holding a fully qualified service type. Values are LinkedList's of ServiceListener's.
     */
    private final ConcurrentMap<String, List<ServiceListenerStatus>> _serviceListeners;

    /**
     * Holds instances of ServiceTypeListener's.
     */
    private final Set<ServiceTypeListenerStatus>                     _typeListeners;

    /**
     * Cache for DNSEntry's.
     */
    private final DNSCache                                           _cache;

    /**
     * This hashtable holds the services that have been registered. Keys are instances of String which hold an all lower-case version of the fully qualified service name. Values are instances of ServiceInfo.
     */
    private final ConcurrentMap<String, ServiceInfo>                 _services;

    /**
     * This hashtable holds the service types that have been registered or that have been received in an incoming datagram.<br/>
     * Keys are instances of String which hold an all lower-case version of the fully qualified service type.<br/>
     * Values hold the fully qualified service type.
     */
    private final ConcurrentMap<String, ServiceTypeEntry>            _serviceTypes;

    private volatile Delegate                                        _delegate;

    /**
     * This is used to store type entries. The type is stored as a call variable and the map support the subtypes.
     * <p>
     * The key is the lowercase version as the value is the case preserved version.
     * </p>
     */
    public static class ServiceTypeEntry extends AbstractMap<String, String> implements Cloneable {

        private final Set<Map.Entry<String, String>> _entrySet;

        private final String                         _type;

        private static class SubTypeEntry implements Entry<String, String>, java.io.Serializable, Cloneable {

            private static final long serialVersionUID = 9188503522395855322L;

            private final String      _key;
            private final String      _value;

            public SubTypeEntry(final String subtype) {
                super();
                this._value = (subtype != null ? subtype : "");
                this._key = this._value.toLowerCase();
            }

            /**
             * {@inheritDoc}
             */
            @Override
            public String getKey() {
                return this._key;
            }

            /**
             * {@inheritDoc}
             */
            @Override
            public String getValue() {
                return this._value;
            }

            /**
             * Replaces the value corresponding to this entry with the specified value (optional operation). This implementation simply throws <tt>UnsupportedOperationException</tt>, as this class implements an <i>immutable</i> map entry.
             * 
             * @param value
             *            new value to be stored in this entry
             * @return (Does not return)
             * @exception UnsupportedOperationException
             *                always
             */
            @Override
            public String setValue(final String value) {
                throw new UnsupportedOperationException();
            }

            /**
             * {@inheritDoc}
             */
            @Override
            public boolean equals(final Object entry) {
                if (!(entry instanceof Map.Entry)) {
                    return false;
                }
                return this.getKey().equals(((Map.Entry<?, ?>) entry).getKey()) && this.getValue().equals(((Map.Entry<?, ?>) entry).getValue());
            }

            /**
             * {@inheritDoc}
             */
            @Override
            public int hashCode() {
                return (this._key == null ? 0 : this._key.hashCode()) ^ (this._value == null ? 0 : this._value.hashCode());
            }

            /*
             * (non-Javadoc)
             * @see java.lang.Object#clone()
             */
            @Override
            public SubTypeEntry clone() {
                // Immutable object
                return this;
            }

            /**
             * {@inheritDoc}
             */
            @Override
            public String toString() {
                return this._key + "=" + this._value;
            }

        }

        public ServiceTypeEntry(final String type) {
            super();
            this._type = type;
            this._entrySet = new HashSet<Map.Entry<String, String>>();
        }

        /**
         * The type associated with this entry.
         * 
         * @return the type
         */
        public String getType() {
            return this._type;
        }

        /*
         * (non-Javadoc)
         * @see java.util.AbstractMap#entrySet()
         */
        @Override
        public Set<Map.Entry<String, String>> entrySet() {
            return this._entrySet;
        }

        /**
         * Returns <code>true</code> if this set contains the specified element. More formally, returns <code>true</code> if and only if this set contains an element <code>e</code> such that
         * <code>(o==null&nbsp;?&nbsp;e==null&nbsp;:&nbsp;o.equals(e))</code>.
         * 
         * @param subtype
         *            element whose presence in this set is to be tested
         * @return <code>true</code> if this set contains the specified element
         */
        public boolean contains(final String subtype) {
            return subtype != null && this.containsKey(subtype.toLowerCase());
        }

        /**
         * Adds the specified element to this set if it is not already present. More formally, adds the specified element <code>e</code> to this set if this set contains no element <code>e2</code> such that
         * <code>(e==null&nbsp;?&nbsp;e2==null&nbsp;:&nbsp;e.equals(e2))</code>. If this set already contains the element, the call leaves the set unchanged and returns <code>false</code>.
         * 
         * @param subtype
         *            element to be added to this set
         * @return <code>true</code> if this set did not already contain the specified element
         */
        public boolean add(final String subtype) {
            if (subtype == null || this.contains(subtype)) {
                return false;
            }
            this._entrySet.add(new SubTypeEntry(subtype));
            return true;
        }

        /**
         * Returns an iterator over the elements in this set. The elements are returned in no particular order (unless this set is an instance of some class that provides a guarantee).
         * 
         * @return an iterator over the elements in this set
         */
        public Iterator<String> iterator() {
            return this.keySet().iterator();
        }

        /*
         * (non-Javadoc)
         * @see java.util.AbstractMap#clone()
         */
        @Override
        public ServiceTypeEntry clone() {
            final ServiceTypeEntry entry = new ServiceTypeEntry(this.getType());
            for (final Map.Entry<String, String> subTypeEntry : this.entrySet()) {
                entry.add(subTypeEntry.getValue());
            }
            return entry;
        }

        /*
         * (non-Javadoc)
         * @see java.util.AbstractMap#toString()
         */
        @Override
        public String toString() {
            final StringBuilder aLog = new StringBuilder(200);
            if (this.isEmpty()) {
                aLog.append("empty");
            } else {
                for (final String value : this.values()) {
                    aLog.append(value);
                    aLog.append(", ");
                }
                aLog.setLength(aLog.length() - 2);
            }
            return aLog.toString();
        }

    }

    /**
     * This is the shutdown hook, we registered with the java runtime.
     */
    protected Thread                                      _shutdown;

    /**
     * Handle on the local host
     */
    private HostInfo                                      _localHost;

    private Thread                                        _incomingListener;

    /**
     * Throttle count. This is used to count the overall number of probes sent by JmDNS. When the last throttle increment happened .
     */
    private int                                           _throttle;

    /**
     * Last throttle increment.
     */
    private long                                          _lastThrottleIncrement;

    private final ExecutorService                         _executor = Executors.newSingleThreadExecutor();

    //
    // 2009-09-16 ldeck: adding docbug patch with slight ammendments
    // 'Fixes two deadlock conditions involving JmDNS.close() - ID: 1473279'
    //
    // ---------------------------------------------------
    /**
     * The timer that triggers our announcements. We can't use the main timer object, because that could cause a deadlock where Prober waits on JmDNS.this lock held by close(), close() waits for us to finish, and we wait for Prober to give us back
     * the timer thread so we can announce. (Patch from docbug in 2006-04-19 still wasn't patched .. so I'm doing it!)
     */
    // private final Timer _cancelerTimer;
    // ---------------------------------------------------

    /**
     * The source for random values. This is used to introduce random delays in responses. This reduces the potential for collisions on the network.
     */
    private final static Random                           _random   = new Random();

    /**
     * This lock is used to coordinate processing of incoming and outgoing messages. This is needed, because the Rendezvous Conformance Test does not forgive race conditions.
     */
    private final ReentrantLock                           _ioLock   = new ReentrantLock();

    /**
     * If an incoming package which needs an answer is truncated, we store it here. We add more incoming DNSRecords to it, until the JmDNS.Responder timer picks it up.<br/>
     * FIXME [PJYF June 8 2010]: This does not work well with multiple planned answers for packages that came in from different clients.
     */
    private DNSIncoming                                   _plannedAnswer;

    // State machine

    /**
     * This hashtable is used to maintain a list of service types being collected by this JmDNS instance. The key of the hashtable is a service type name, the value is an instance of JmDNS.ServiceCollector.
     * 
     * @see #list
     */
    private final ConcurrentMap<String, ServiceCollector> _serviceCollectors;

    private final String                                  _name;

    /**
     * Main method to display API information if run from java -jar
     * 
     * @param argv
     *            the command line arguments
     */
    public static void main(final String[] argv) {
        String version = null;
        try {
            final Properties pomProperties = new Properties();
            pomProperties.load(JmDNSImpl.class.getResourceAsStream("/META-INF/maven/javax.jmdns/jmdns/pom.properties"));
            version = pomProperties.getProperty("version");
        } catch (final Exception e) {
            version = "RUNNING.IN.IDE.FULL";
        }
        System.out.println("JmDNS version \"" + version + "\"");
        System.out.println(" ");

        System.out.println("Running on java version \"" + System.getProperty("java.version") + "\"" + " (build " + System.getProperty("java.runtime.version") + ")" + " from " + System.getProperty("java.vendor"));

        System.out.println("Operating environment \"" + System.getProperty("os.name") + "\"" + " version " + System.getProperty("os.version") + " on " + System.getProperty("os.arch"));

        System.out.println("For more information on JmDNS please visit https://sourceforge.net/projects/jmdns/");
    }

    /**
     * Create an instance of JmDNS and bind it to a specific network interface given its IP-address.
     * 
     * @param address
     *            IP address to bind to.
     * @param name
     *            name of the newly created JmDNS
     * @exception IOException
     */
    public JmDNSImpl(final InetAddress address, final String name) throws IOException {
        super();
        if (logger.isLoggable(Level.FINER)) {
            logger.finer("JmDNS instance created");
        }
        this._cache = new DNSCache(100);

        this._listeners = Collections.synchronizedList(new ArrayList<DNSListener>());
        this._serviceListeners = new ConcurrentHashMap<String, List<ServiceListenerStatus>>();
        this._typeListeners = Collections.synchronizedSet(new HashSet<ServiceTypeListenerStatus>());
        this._serviceCollectors = new ConcurrentHashMap<String, ServiceCollector>();

        this._services = new ConcurrentHashMap<String, ServiceInfo>(20);
        this._serviceTypes = new ConcurrentHashMap<String, ServiceTypeEntry>(20);

        this._localHost = HostInfo.newHostInfo(address, this, name);
        this._name = (name != null ? name : this._localHost.getName());

        // _cancelerTimer = new Timer("JmDNS.cancelerTimer");

        // (ldeck 2.1.1) preventing shutdown blocking thread
        // -------------------------------------------------
        // _shutdown = new Thread(new Shutdown(), "JmDNS.Shutdown");
        // Runtime.getRuntime().addShutdownHook(_shutdown);

        // -------------------------------------------------

        // Bind to multicast socket
        this.openMulticastSocket(this.getLocalHost());
        this.start(this.getServices().values());

        this.startReaper();
    }

    private void start(final Collection<? extends ServiceInfo> serviceInfos) {
        if (this._incomingListener == null) {
            this._incomingListener = new SocketListener(this);
            this._incomingListener.start();
        }
        this.startProber();
        for (final ServiceInfo info : serviceInfos) {
            try {
                this.registerService(new ServiceInfoImpl(info));
            } catch (final Exception exception) {
                logger.log(Level.WARNING, "start() Registration exception ", exception);
            }
        }
    }

    private void openMulticastSocket(final HostInfo hostInfo) throws IOException {
        if (this._group == null) {
            if (hostInfo.getInetAddress() instanceof Inet6Address) {
                this._group = InetAddress.getByName(DNSConstants.MDNS_GROUP_IPV6);
            } else {
                this._group = InetAddress.getByName(DNSConstants.MDNS_GROUP);
            }
        }
        if (this._socket != null) {
            this.closeMulticastSocket();
        }
        this._socket = new MulticastSocket(DNSConstants.MDNS_PORT);
        if ((hostInfo != null) && (hostInfo.getInterface() != null)) {
            try {
                this._socket.setNetworkInterface(hostInfo.getInterface());
            } catch (final SocketException e) {
                if (logger.isLoggable(Level.FINE)) {
                    logger.fine("openMulticastSocket() Set network interface exception: " + e.getMessage());
                }
            }
        }
        this._socket.setTimeToLive(255);
        this._socket.joinGroup(this._group);
    }

    private void closeMulticastSocket() {
        // jP: 20010-01-18. See below. We'll need this monitor...
        // assert (Thread.holdsLock(this));
        if (logger.isLoggable(Level.FINER)) {
            logger.finer("closeMulticastSocket()");
        }
        if (this._socket != null) {
            // close socket
            try {
                try {
                    this._socket.leaveGroup(this._group);
                } catch (final SocketException exception) {
                    //
                }
                this._socket.close();
                // jP: 20010-01-18. It isn't safe to join() on the listener
                // thread - it attempts to lock the IoLock object, and deadlock
                // ensues. Per issue #2933183, changed this to wait on the JmDNS
                // monitor, checking on each notify (or timeout) that the
                // listener thread has stopped.
                //
                while (this._incomingListener != null && this._incomingListener.isAlive()) {
                    synchronized (this) {
                        try {
                            if (this._incomingListener != null && this._incomingListener.isAlive()) {
                                // wait time is arbitrary, we're really expecting notification.
                                if (logger.isLoggable(Level.FINER)) {
                                    logger.finer("closeMulticastSocket(): waiting for jmDNS monitor");
                                }
                                this.wait(1000);
                            }
                        } catch (final InterruptedException ignored) {
                            // Ignored
                        }
                    }
                }
                this._incomingListener = null;
            } catch (final Exception exception) {
                logger.log(Level.WARNING, "closeMulticastSocket() Close socket exception ", exception);
            }
            this._socket = null;
        }
    }

    // State machine
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean advanceState(final DNSTask task) {
        return this._localHost.advanceState(task);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean revertState() {
        return this._localHost.revertState();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean cancelState() {
        return this._localHost.cancelState();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean closeState() {
        return this._localHost.closeState();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean recoverState() {
        return this._localHost.recoverState();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JmDNSImpl getDns() {
        return this;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void associateWithTask(final DNSTask task, final DNSState state) {
        this._localHost.associateWithTask(task, state);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeAssociationWithTask(final DNSTask task) {
        this._localHost.removeAssociationWithTask(task);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isAssociatedWithTask(final DNSTask task, final DNSState state) {
        return this._localHost.isAssociatedWithTask(task, state);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isProbing() {
        return this._localHost.isProbing();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isAnnouncing() {
        return this._localHost.isAnnouncing();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isAnnounced() {
        return this._localHost.isAnnounced();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isCanceling() {
        return this._localHost.isCanceling();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isCanceled() {
        return this._localHost.isCanceled();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isClosing() {
        return this._localHost.isClosing();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isClosed() {
        return this._localHost.isClosed();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean waitForAnnounced(final long timeout) {
        return this._localHost.waitForAnnounced(timeout);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean waitForCanceled(final long timeout) {
        return this._localHost.waitForCanceled(timeout);
    }

    /**
     * Return the DNSCache associated with the cache variable
     * 
     * @return DNS cache
     */
    public DNSCache getCache() {
        return this._cache;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getName() {
        return this._name;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getHostName() {
        return this._localHost.getName();
    }

    /**
     * Returns the local host info
     * 
     * @return local host info
     */
    public HostInfo getLocalHost() {
        return this._localHost;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public InetAddress getInterface() throws IOException {
        return this._socket.getInterface();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ServiceInfo getServiceInfo(final String type, final String name) {
        return this.getServiceInfo(type, name, false, DNSConstants.SERVICE_INFO_TIMEOUT);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ServiceInfo getServiceInfo(final String type, final String name, final long timeout) {
        return this.getServiceInfo(type, name, false, timeout);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ServiceInfo getServiceInfo(final String type, final String name, final boolean persistent) {
        return this.getServiceInfo(type, name, persistent, DNSConstants.SERVICE_INFO_TIMEOUT);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ServiceInfo getServiceInfo(final String type, final String name, final boolean persistent, final long timeout) {
        final ServiceInfoImpl info = this.resolveServiceInfo(type, name, "", persistent);
        this.waitForInfoData(info, timeout);
        return (info.hasData() ? info : null);
    }

    ServiceInfoImpl resolveServiceInfo(final String type, final String name, final String subtype, final boolean persistent) {
        this.cleanCache();
        final String loType = type.toLowerCase();
        this.registerServiceType(type);
        if (this._serviceCollectors.putIfAbsent(loType, new ServiceCollector(type)) == null) {
            this.addServiceListener(loType, this._serviceCollectors.get(loType), ListenerStatus.SYNCHONEOUS);
        }

        // Check if the answer is in the cache.
        final ServiceInfoImpl info = this.getServiceInfoFromCache(type, name, subtype, persistent);
        // We still run the resolver to do the dispatch but if the info is already there it will quit immediately
        this.startServiceInfoResolver(info);

        return info;
    }

    ServiceInfoImpl getServiceInfoFromCache(final String type, final String name, final String subtype, final boolean persistent) {
        // Check if the answer is in the cache.
        ServiceInfoImpl info = new ServiceInfoImpl(type, name, subtype, 0, 0, 0, persistent, (byte[]) null);
        final DNSEntry pointerEntry = this.getCache().getDNSEntry(new DNSRecord.Pointer(type, DNSRecordClass.CLASS_ANY, false, 0, info.getQualifiedName()));
        if (pointerEntry instanceof DNSRecord) {
            ServiceInfoImpl cachedInfo = (ServiceInfoImpl) ((DNSRecord) pointerEntry).getServiceInfo(persistent);
            if (cachedInfo != null) {
                // To get a complete info record we need to retrieve the service, address and the text bytes.

                final Map<Fields, String> map = cachedInfo.getQualifiedNameMap();
                byte[] srvBytes = null;
                String server = "";
                final DNSEntry serviceEntry = this.getCache().getDNSEntry(info.getQualifiedName(), DNSRecordType.TYPE_SRV, DNSRecordClass.CLASS_ANY);
                if (serviceEntry instanceof DNSRecord) {
                    final ServiceInfo cachedServiceEntryInfo = ((DNSRecord) serviceEntry).getServiceInfo(persistent);
                    if (cachedServiceEntryInfo != null) {
                        cachedInfo = new ServiceInfoImpl(map, cachedServiceEntryInfo.getPort(), cachedServiceEntryInfo.getWeight(), cachedServiceEntryInfo.getPriority(), persistent, (byte[]) null);
                        srvBytes = cachedServiceEntryInfo.getTextBytes();
                        server = cachedServiceEntryInfo.getServer();
                    }
                }
                DNSEntry addressEntry = this.getCache().getDNSEntry(server, DNSRecordType.TYPE_A, DNSRecordClass.CLASS_ANY);
                if (addressEntry instanceof DNSRecord) {
                    final ServiceInfo cachedAddressInfo = ((DNSRecord) addressEntry).getServiceInfo(persistent);
                    if (cachedAddressInfo != null) {
                        for (final Inet4Address address : cachedAddressInfo.getInet4Addresses()) {
                            cachedInfo.addAddress(address);
                        }
                        cachedInfo._setText(cachedAddressInfo.getTextBytes());
                    }
                }
                addressEntry = this.getCache().getDNSEntry(server, DNSRecordType.TYPE_AAAA, DNSRecordClass.CLASS_ANY);
                if (addressEntry instanceof DNSRecord) {
                    final ServiceInfo cachedAddressInfo = ((DNSRecord) addressEntry).getServiceInfo(persistent);
                    if (cachedAddressInfo != null) {
                        for (final Inet6Address address : cachedAddressInfo.getInet6Addresses()) {
                            cachedInfo.addAddress(address);
                        }
                        cachedInfo._setText(cachedAddressInfo.getTextBytes());
                    }
                }
                final DNSEntry textEntry = this.getCache().getDNSEntry(cachedInfo.getQualifiedName(), DNSRecordType.TYPE_TXT, DNSRecordClass.CLASS_ANY);
                if (textEntry instanceof DNSRecord) {
                    final ServiceInfo cachedTextInfo = ((DNSRecord) textEntry).getServiceInfo(persistent);
                    if (cachedTextInfo != null) {
                        cachedInfo._setText(cachedTextInfo.getTextBytes());
                    }
                }
                if (cachedInfo.getTextBytes().length == 0) {
                    cachedInfo._setText(srvBytes);
                }
                if (cachedInfo.hasData()) {
                    info = cachedInfo;
                }
            }
        }
        return info;
    }

    private void waitForInfoData(final ServiceInfo info, final long timeout) {
        synchronized (info) {
            long loops = (timeout / 200L);
            if (loops < 1) {
                loops = 1;
            }
            for (int i = 0; i < loops; i++) {
                if (info.hasData()) {
                    break;
                }
                try {
                    info.wait(200);
                } catch (final InterruptedException e) {
                    /* Stub */
                }
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void requestServiceInfo(final String type, final String name) {
        this.requestServiceInfo(type, name, false, DNSConstants.SERVICE_INFO_TIMEOUT);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void requestServiceInfo(final String type, final String name, final boolean persistent) {
        this.requestServiceInfo(type, name, persistent, DNSConstants.SERVICE_INFO_TIMEOUT);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void requestServiceInfo(final String type, final String name, final long timeout) {
        this.requestServiceInfo(type, name, false, DNSConstants.SERVICE_INFO_TIMEOUT);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void requestServiceInfo(final String type, final String name, final boolean persistent, final long timeout) {
        final ServiceInfoImpl info = this.resolveServiceInfo(type, name, "", persistent);
        this.waitForInfoData(info, timeout);
    }

    void handleServiceResolved(final ServiceEvent event) {
        final List<ServiceListenerStatus> list = this._serviceListeners.get(event.getType().toLowerCase());
        final List<ServiceListenerStatus> listCopy;
        if ((list != null) && (!list.isEmpty())) {
            if ((event.getInfo() != null) && event.getInfo().hasData()) {
                final ServiceEvent localEvent = event;
                synchronized (list) {
                    listCopy = new ArrayList<ServiceListenerStatus>(list);
                }
                for (final ServiceListenerStatus listener : listCopy) {
                    if (this._executor.isShutdown()) {
                        break;
                    }
                    this._executor.submit(new Runnable() {
                        /** {@inheritDoc} */
                        @Override
                        public void run() {
                            listener.serviceResolved(localEvent);
                        }
                    });
                }
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void addServiceTypeListener(final ServiceTypeListener listener) throws IOException {
        final ServiceTypeListenerStatus status = new ServiceTypeListenerStatus(listener, ListenerStatus.ASYNCHONEOUS);
        this._typeListeners.add(status);

        // report cached service types
        for (final String type : this._serviceTypes.keySet()) {
            status.serviceTypeAdded(new ServiceEventImpl(this, type, "", null));
        }

        this.startTypeResolver();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeServiceTypeListener(final ServiceTypeListener listener) {
        final ServiceTypeListenerStatus status = new ServiceTypeListenerStatus(listener, ListenerStatus.ASYNCHONEOUS);
        this._typeListeners.remove(status);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void addServiceListener(final String type, final ServiceListener listener) {
        this.addServiceListener(type, listener, ListenerStatus.ASYNCHONEOUS);
    }

    private void addServiceListener(final String type, final ServiceListener listener, final boolean synch) {
        final ServiceListenerStatus status = new ServiceListenerStatus(listener, synch);
        final String loType = type.toLowerCase();
        List<ServiceListenerStatus> list = this._serviceListeners.get(loType);
        if (list == null) {
            if (this._serviceListeners.putIfAbsent(loType, new LinkedList<ServiceListenerStatus>()) == null) {
                if (this._serviceCollectors.putIfAbsent(loType, new ServiceCollector(type)) == null) {
                    // We have a problem here. The service collectors must be called synchronously so that their cache get cleaned up immediately or we will report .
                    this.addServiceListener(loType, this._serviceCollectors.get(loType), ListenerStatus.SYNCHONEOUS);
                }
            }
            list = this._serviceListeners.get(loType);
        }
        if (list != null) {
            synchronized (list) {
                if (!list.contains(listener)) {
                    list.add(status);
                }
            }
        }
        // report cached service types
        final List<ServiceEvent> serviceEvents = new ArrayList<ServiceEvent>();
        final Collection<DNSEntry> dnsEntryLits = this.getCache().allValues();
        for (final DNSEntry entry : dnsEntryLits) {
            final DNSRecord record = (DNSRecord) entry;
            if (record.getRecordType() == DNSRecordType.TYPE_SRV) {
                if (record.getKey().endsWith(loType)) {
                    // Do not used the record embedded method for generating event this will not work.
                    // serviceEvents.add(record.getServiceEvent(this));
                    serviceEvents.add(new ServiceEventImpl(this, record.getType(), toUnqualifiedName(record.getType(), record.getName()), record.getServiceInfo()));
                }
            }
        }
        // Actually call listener with all service events added above
        for (final ServiceEvent serviceEvent : serviceEvents) {
            status.serviceAdded(serviceEvent);
        }
        // Create/start ServiceResolver
        this.startServiceResolver(type);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeServiceListener(final String type, final ServiceListener listener) {
        final String loType = type.toLowerCase();
        final List<ServiceListenerStatus> list = this._serviceListeners.get(loType);
        if (list != null) {
            synchronized (list) {
                final ServiceListenerStatus status = new ServiceListenerStatus(listener, ListenerStatus.ASYNCHONEOUS);
                list.remove(status);
                if (list.isEmpty()) {
                    this._serviceListeners.remove(loType, list);
                }
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void registerService(final ServiceInfo infoAbstract) throws IOException {
        if (this.isClosing() || this.isClosed()) {
            throw new IllegalStateException("This DNS is closed.");
        }
        final ServiceInfoImpl info = (ServiceInfoImpl) infoAbstract;

        if (info.getDns() != null) {
            if (info.getDns() != this) {
                throw new IllegalStateException("A service information can only be registered with a single instamce of JmDNS.");
            } else if (this._services.get(info.getKey()) != null) {
                throw new IllegalStateException("A service information can only be registered once.");
            }
        }
        info.setDns(this);

        this.registerServiceType(info.getTypeWithSubtype());

        // bind the service to this address
        info.recoverState();
        info.setServer(this._localHost.getName());
        info.addAddress(this._localHost.getInet4Address());
        info.addAddress(this._localHost.getInet6Address());

        this.waitForAnnounced(DNSConstants.SERVICE_INFO_TIMEOUT);

        this.makeServiceNameUnique(info);
        while (this._services.putIfAbsent(info.getKey(), info) != null) {
            this.makeServiceNameUnique(info);
        }

        this.startProber();
        info.waitForAnnounced(DNSConstants.SERVICE_INFO_TIMEOUT);

        if (logger.isLoggable(Level.FINE)) {
            logger.fine("registerService() JmDNS registered service as " + info);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void unregisterService(final ServiceInfo infoAbstract) {
        final ServiceInfoImpl info = (ServiceInfoImpl) this._services.get(infoAbstract.getKey());

        if (info != null) {
            info.cancelState();
            this.startCanceler();
            info.waitForCanceled(DNSConstants.CLOSE_TIMEOUT);

            this._services.remove(info.getKey(), info);
            if (logger.isLoggable(Level.FINE)) {
                logger.fine("unregisterService() JmDNS unregistered service as " + info);
            }
        } else {
            logger.warning("Removing unregistered service info: " + infoAbstract.getKey());
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void unregisterAllServices() {
        if (logger.isLoggable(Level.FINER)) {
            logger.finer("unregisterAllServices()");
        }

        for (final String name : this._services.keySet()) {
            final ServiceInfoImpl info = (ServiceInfoImpl) this._services.get(name);
            if (info != null) {
                if (logger.isLoggable(Level.FINER)) {
                    logger.finer("Cancelling service info: " + info);
                }
                info.cancelState();
            }
        }
        this.startCanceler();

        for (final String name : this._services.keySet()) {
            final ServiceInfoImpl info = (ServiceInfoImpl) this._services.get(name);
            if (info != null) {
                if (logger.isLoggable(Level.FINER)) {
                    logger.finer("Wait for service info cancel: " + info);
                }
                info.waitForCanceled(DNSConstants.CLOSE_TIMEOUT);
                this._services.remove(name, info);
            }
        }

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean registerServiceType(final String type) {
        boolean typeAdded = false;
        final Map<Fields, String> map = ServiceInfoImpl.decodeQualifiedNameMapForType(type);
        final String domain = map.get(Fields.Domain);
        final String protocol = map.get(Fields.Protocol);
        final String application = map.get(Fields.Application);
        final String subtype = map.get(Fields.Subtype);

        final String name = (application.length() > 0 ? "_" + application + "." : "") + (protocol.length() > 0 ? "_" + protocol + "." : "") + domain + ".";
        final String loname = name.toLowerCase();
        if (logger.isLoggable(Level.FINE)) {
            logger.fine(this.getName() + ".registering service type: " + type + " as: " + name + (subtype.length() > 0 ? " subtype: " + subtype : ""));
        }
        if (!this._serviceTypes.containsKey(loname) && !application.toLowerCase().equals("dns-sd") && !domain.toLowerCase().endsWith("in-addr.arpa") && !domain.toLowerCase().endsWith("ip6.arpa")) {
            typeAdded = this._serviceTypes.putIfAbsent(loname, new ServiceTypeEntry(name)) == null;
            if (typeAdded) {
                final ServiceTypeListenerStatus[] list = this._typeListeners.toArray(new ServiceTypeListenerStatus[this._typeListeners.size()]);
                final ServiceEvent event = new ServiceEventImpl(this, name, "", null);
                for (final ServiceTypeListenerStatus status : list) {
                    if (this._executor.isShutdown()) {
                        break;
                    }
                    this._executor.submit(new Runnable() {
                        /** {@inheritDoc} */
                        @Override
                        public void run() {
                            status.serviceTypeAdded(event);
                        }
                    });
                }
            }
        }
        if (subtype.length() > 0) {
            final ServiceTypeEntry subtypes = this._serviceTypes.get(loname);
            if ((subtypes != null) && (!subtypes.contains(subtype))) {
                synchronized (subtypes) {
                    if (!subtypes.contains(subtype)) {
                        typeAdded = true;
                        subtypes.add(subtype);
                        final ServiceTypeListenerStatus[] list = this._typeListeners.toArray(new ServiceTypeListenerStatus[this._typeListeners.size()]);
                        final ServiceEvent event = new ServiceEventImpl(this, "_" + subtype + "._sub." + name, "", null);
                        for (final ServiceTypeListenerStatus status : list) {
                            if (this._executor.isShutdown()) {
                                break;
                            }
                            this._executor.submit(new Runnable() {
                                /** {@inheritDoc} */
                                @Override
                                public void run() {
                                    status.subTypeForServiceTypeAdded(event);
                                }
                            });
                        }
                    }
                }
            }
        }
        return typeAdded;
    }

    /**
     * Generate a possibly unique name for a service using the information we have in the cache.
     * 
     * @return returns true, if the name of the service info had to be changed.
     */
    private boolean makeServiceNameUnique(final ServiceInfoImpl info) {
        final String originalQualifiedName = info.getKey();
        final long now = System.currentTimeMillis();

        boolean collision;
        do {
            collision = false;

            // Check for collision in cache
            for (final DNSEntry dnsEntry : this.getCache().getDNSEntryList(info.getKey())) {
                if (DNSRecordType.TYPE_SRV.equals(dnsEntry.getRecordType()) && !dnsEntry.isExpired(now)) {
                    final DNSRecord.Service s = (DNSRecord.Service) dnsEntry;
                    if (s.getPort() != info.getPort() || !s.getServer().equals(this._localHost.getName())) {
                        if (logger.isLoggable(Level.FINER)) {
                            logger.finer("makeServiceNameUnique() JmDNS.makeServiceNameUnique srv collision:" + dnsEntry + " s.server=" + s.getServer() + " " + this._localHost.getName() + " equals:"
                                    + (s.getServer().equals(this._localHost.getName())));
                        }
                        info.setName(this.incrementName(info.getName()));
                        collision = true;
                        break;
                    }
                }
            }

            // Check for collision with other service infos published by JmDNS
            final ServiceInfo selfService = this._services.get(info.getKey());
            if (selfService != null && selfService != info) {
                info.setName(this.incrementName(info.getName()));
                collision = true;
            }
        }
        while (collision);

        return !(originalQualifiedName.equals(info.getKey()));
    }

    String incrementName(final String name) {
        String aName = name;
        try {
            final int l = aName.lastIndexOf('(');
            final int r = aName.lastIndexOf(')');
            if ((l >= 0) && (l < r)) {
                aName = aName.substring(0, l) + "(" + (Integer.parseInt(aName.substring(l + 1, r)) + 1) + ")";
            } else {
                aName += " (2)";
            }
        } catch (final NumberFormatException e) {
            aName += " (2)";
        }
        return aName;
    }

    /**
     * Add a listener for a question. The listener will receive updates of answers to the question as they arrive, or from the cache if they are already available.
     * 
     * @param listener
     *            DSN listener
     * @param question
     *            DNS query
     */
    public void addListener(final DNSListener listener, final DNSQuestion question) {
        final long now = System.currentTimeMillis();

        // add the new listener
        this._listeners.add(listener);

        // report existing matched records

        if (question != null) {
            for (final DNSEntry dnsEntry : this.getCache().getDNSEntryList(question.getName().toLowerCase())) {
                if (question.answeredBy(dnsEntry) && !dnsEntry.isExpired(now)) {
                    listener.updateRecord(this.getCache(), now, dnsEntry);
                }
            }
        }
    }

    /**
     * Remove a listener from all outstanding questions. The listener will no longer receive any updates.
     * 
     * @param listener
     *            DSN listener
     */
    public void removeListener(final DNSListener listener) {
        this._listeners.remove(listener);
    }

    /**
     * Renew a service when the record become stale. If there is no service collector for the type this method does nothing.
     * 
     * @param record
     *            DNS record
     */
    public void renewServiceCollector(final DNSRecord record) {
        final ServiceInfo info = record.getServiceInfo();
        if (this._serviceCollectors.containsKey(info.getType().toLowerCase())) {
            // Create/start ServiceResolver
            this.startServiceResolver(info.getType());
        }
    }

    // Remind: Method updateRecord should receive a better name.
    /**
     * Notify all listeners that a record was updated.
     * 
     * @param now
     *            update date
     * @param rec
     *            DNS record
     * @param operation
     *            DNS cache operation
     */
    public void updateRecord(final long now, final DNSRecord rec, final Operation operation) {
        // We do not want to block the entire DNS while we are updating the record for each listener (service info)
        {
            List<DNSListener> listenerList = null;
            synchronized (this._listeners) {
                listenerList = new ArrayList<DNSListener>(this._listeners);
            }
            for (final DNSListener listener : listenerList) {
                listener.updateRecord(this.getCache(), now, rec);
            }
        }
        if (DNSRecordType.TYPE_PTR.equals(rec.getRecordType()))
        // if (DNSRecordType.TYPE_PTR.equals(rec.getRecordType()) || DNSRecordType.TYPE_SRV.equals(rec.getRecordType()))
        {
            ServiceEvent event = rec.getServiceEvent(this);
            if ((event.getInfo() == null) || !event.getInfo().hasData()) {
                // We do not care about the subtype because the info is only used if complete and the subtype will then be included.
                final ServiceInfo info = this.getServiceInfoFromCache(event.getType(), event.getName(), "", false);
                if (info.hasData()) {
                    event = new ServiceEventImpl(this, event.getType(), event.getName(), info);
                }
            }

            final List<ServiceListenerStatus> list = this._serviceListeners.get(event.getType().toLowerCase());
            final List<ServiceListenerStatus> serviceListenerList;
            if (list != null) {
                synchronized (list) {
                    serviceListenerList = new ArrayList<ServiceListenerStatus>(list);
                }
            } else {
                serviceListenerList = Collections.emptyList();
            }
            if (logger.isLoggable(Level.FINEST)) {
                logger.finest(this.getName() + ".updating record for event: " + event + " list " + serviceListenerList + " operation: " + operation);
            }
            if (!serviceListenerList.isEmpty()) {
                final ServiceEvent localEvent = event;

                switch (operation) {
                    case Add:
                        for (final ServiceListenerStatus listener : serviceListenerList) {
                            if (listener.isSynchronous()) {
                                listener.serviceAdded(localEvent);
                            } else if (!this._executor.isShutdown()) {
                                this._executor.submit(new Runnable() {
                                    /** {@inheritDoc} */
                                    @Override
                                    public void run() {
                                        listener.serviceAdded(localEvent);
                                    }
                                });
                            }
                        }
                        break;
                    case Remove:
                        for (final ServiceListenerStatus listener : serviceListenerList) {
                            if (listener.isSynchronous()) {
                                listener.serviceRemoved(localEvent);
                            } else if (!this._executor.isShutdown()) {
                                this._executor.submit(new Runnable() {
                                    /** {@inheritDoc} */
                                    @Override
                                    public void run() {
                                        listener.serviceRemoved(localEvent);
                                    }
                                });
                            }
                        }
                        break;
                    default:
                        break;
                }
            }
        }
    }

    void handleRecord(final DNSRecord record, final long now) {
        DNSRecord newRecord = record;

        Operation cacheOperation = Operation.Noop;
        final boolean expired = newRecord.isExpired(now);
        if (logger.isLoggable(Level.FINE)) {
            logger.fine(this.getName() + " handle response: " + newRecord);
        }

        // update the cache
        if (!newRecord.isServicesDiscoveryMetaQuery() && !newRecord.isDomainDiscoveryQuery()) {
            final boolean unique = newRecord.isUnique();
            final DNSRecord cachedRecord = (DNSRecord) this.getCache().getDNSEntry(newRecord);
            if (logger.isLoggable(Level.FINE)) {
                logger.fine(this.getName() + " handle response cached record: " + cachedRecord);
            }
            if (unique) {
                for (final DNSEntry entry : this.getCache().getDNSEntryList(newRecord.getKey())) {
                    if (newRecord.getRecordType().equals(entry.getRecordType()) && newRecord.getRecordClass().equals(entry.getRecordClass()) && (entry != cachedRecord)) {
                        ((DNSRecord) entry).setWillExpireSoon(now);
                    }
                }
            }
            if (cachedRecord != null) {
                if (expired) {
                    // if the record has a 0 ttl that means we have a cancel record we need to delay the removal by 1s
                    if (newRecord.getTTL() == 0) {
                        cacheOperation = Operation.Noop;
                        cachedRecord.setWillExpireSoon(now);
                        // the actual record will be disposed of by the record reaper.
                    } else {
                        cacheOperation = Operation.Remove;
                        this.getCache().removeDNSEntry(cachedRecord);
                    }
                } else {
                    // If the record content has changed we need to inform our listeners.
                    if (!newRecord.sameValue(cachedRecord) || (!newRecord.sameSubtype(cachedRecord) && (newRecord.getSubtype().length() > 0))) {
                        if (newRecord.isSingleValued()) {
                            cacheOperation = Operation.Update;
                            this.getCache().replaceDNSEntry(newRecord, cachedRecord);
                        } else {
                            // Address record can have more than one value on multi-homed machines
                            cacheOperation = Operation.Add;
                            this.getCache().addDNSEntry(newRecord);
                        }
                    } else {
                        cachedRecord.resetTTL(newRecord);
                        newRecord = cachedRecord;
                    }
                }
            } else {
                if (!expired) {
                    cacheOperation = Operation.Add;
                    this.getCache().addDNSEntry(newRecord);
                }
            }
        }

        // Register new service types
        if (newRecord.getRecordType() == DNSRecordType.TYPE_PTR) {
            // handle DNSConstants.DNS_META_QUERY records
            boolean typeAdded = false;
            if (newRecord.isServicesDiscoveryMetaQuery()) {
                // The service names are in the alias.
                if (!expired) {
                    typeAdded = this.registerServiceType(((DNSRecord.Pointer) newRecord).getAlias());
                }
                return;
            }
            typeAdded |= this.registerServiceType(newRecord.getName());
            if (typeAdded && (cacheOperation == Operation.Noop)) {
                cacheOperation = Operation.RegisterServiceType;
            }
        }

        // notify the listeners
        if (cacheOperation != Operation.Noop) {
            this.updateRecord(now, newRecord, cacheOperation);
        }

    }

    /**
     * Handle an incoming response. Cache answers, and pass them on to the appropriate questions.
     * 
     * @exception IOException
     */
    void handleResponse(final DNSIncoming msg) throws IOException {
        final long now = System.currentTimeMillis();

        boolean hostConflictDetected = false;
        boolean serviceConflictDetected = false;

        for (final DNSRecord newRecord : msg.getAllAnswers()) {
            this.handleRecord(newRecord, now);

            if (DNSRecordType.TYPE_A.equals(newRecord.getRecordType()) || DNSRecordType.TYPE_AAAA.equals(newRecord.getRecordType())) {
                hostConflictDetected |= newRecord.handleResponse(this);
            } else {
                serviceConflictDetected |= newRecord.handleResponse(this);
            }

        }

        if (hostConflictDetected || serviceConflictDetected) {
            this.startProber();
        }
    }

    /**
     * Handle an incoming query. See if we can answer any part of it given our service infos.
     * 
     * @param in
     * @param addr
     * @param port
     * @exception IOException
     */
    void handleQuery(final DNSIncoming in, final InetAddress addr, final int port) throws IOException {
        if (logger.isLoggable(Level.FINE)) {
            logger.fine(this.getName() + ".handle query: " + in);
        }
        // Track known answers
        boolean conflictDetected = false;
        final long expirationTime = System.currentTimeMillis() + DNSConstants.KNOWN_ANSWER_TTL;
        for (final DNSRecord answer : in.getAllAnswers()) {
            conflictDetected |= answer.handleQuery(this, expirationTime);
        }

        this.ioLock();
        try {

            if (this._plannedAnswer != null) {
                this._plannedAnswer.append(in);
            } else {
                final DNSIncoming plannedAnswer = in.clone();
                if (in.isTruncated()) {
                    this._plannedAnswer = plannedAnswer;
                }
                this.startResponder(plannedAnswer, port);
            }

        } finally {
            this.ioUnlock();
        }

        final long now = System.currentTimeMillis();
        for (final DNSRecord answer : in.getAnswers()) {
            this.handleRecord(answer, now);
        }

        if (conflictDetected) {
            this.startProber();
        }
    }

    public void respondToQuery(final DNSIncoming in) {
        this.ioLock();
        try {
            if (this._plannedAnswer == in) {
                this._plannedAnswer = null;
            }
        } finally {
            this.ioUnlock();
        }
    }

    /**
     * Add an answer to a question. Deal with the case when the outgoing packet overflows
     * 
     * @param in
     * @param addr
     * @param port
     * @param out
     * @param rec
     * @return outgoing answer
     * @exception IOException
     */
    public DNSOutgoing addAnswer(final DNSIncoming in, final InetAddress addr, final int port, final DNSOutgoing out, final DNSRecord rec) throws IOException {
        DNSOutgoing newOut = out;
        if (newOut == null) {
            newOut = new DNSOutgoing(DNSConstants.FLAGS_QR_RESPONSE | DNSConstants.FLAGS_AA, false, in.getSenderUDPPayload());
        }
        try {
            newOut.addAnswer(in, rec);
        } catch (final IOException e) {
            newOut.setFlags(newOut.getFlags() | DNSConstants.FLAGS_TC);
            newOut.setId(in.getId());
            this.send(newOut);

            newOut = new DNSOutgoing(DNSConstants.FLAGS_QR_RESPONSE | DNSConstants.FLAGS_AA, false, in.getSenderUDPPayload());
            newOut.addAnswer(in, rec);
        }
        return newOut;
    }

    /**
     * Send an outgoing multicast DNS message.
     * 
     * @param out
     * @exception IOException
     */
    public void send(final DNSOutgoing out) throws IOException {
        if (!out.isEmpty()) {
            final byte[] message = out.data();
            final DatagramPacket packet = new DatagramPacket(message, message.length, this._group, DNSConstants.MDNS_PORT);

            if (logger.isLoggable(Level.FINEST)) {
                try {
                    final DNSIncoming msg = new DNSIncoming(packet);
                    if (logger.isLoggable(Level.FINEST)) {
                        logger.finest("send(" + this.getName() + ") JmDNS out:" + msg.print(true));
                    }
                } catch (final IOException e) {
                    logger.throwing(this.getClass().toString(), "send(" + this.getName() + ") - JmDNS can not parse what it sends!!!", e);
                }
            }
            final MulticastSocket ms = this._socket;
            if (ms != null && !ms.isClosed()) {
                ms.send(packet);
            }
        }
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#purgeTimer()
     */
    @Override
    public void purgeTimer() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).purgeTimer();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#purgeStateTimer()
     */
    @Override
    public void purgeStateTimer() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).purgeStateTimer();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#cancelTimer()
     */
    @Override
    public void cancelTimer() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).cancelTimer();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#cancelStateTimer()
     */
    @Override
    public void cancelStateTimer() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).cancelStateTimer();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startProber()
     */
    @Override
    public void startProber() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startProber();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startAnnouncer()
     */
    @Override
    public void startAnnouncer() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startAnnouncer();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startRenewer()
     */
    @Override
    public void startRenewer() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startRenewer();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startCanceler()
     */
    @Override
    public void startCanceler() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startCanceler();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startReaper()
     */
    @Override
    public void startReaper() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startReaper();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startServiceInfoResolver(javax.jmdns.impl.ServiceInfoImpl)
     */
    @Override
    public void startServiceInfoResolver(final ServiceInfoImpl info) {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startServiceInfoResolver(info);
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startTypeResolver()
     */
    @Override
    public void startTypeResolver() {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startTypeResolver();
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startServiceResolver(java.lang.String)
     */
    @Override
    public void startServiceResolver(final String type) {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startServiceResolver(type);
    }

    /*
     * (non-Javadoc)
     * @see javax.jmdns.impl.DNSTaskStarter#startResponder(javax.jmdns.impl.DNSIncoming, int)
     */
    @Override
    public void startResponder(final DNSIncoming in, final int port) {
        DNSTaskStarter.Factory.getInstance().getStarter(this.getDns()).startResponder(in, port);
    }

    // REMIND: Why is this not an anonymous inner class?
    /**
     * Shutdown operations.
     */
    protected class Shutdown implements Runnable {
        /** {@inheritDoc} */
        @Override
        public void run() {
            try {
                JmDNSImpl.this._shutdown = null;
                JmDNSImpl.this.close();
            } catch (final Throwable exception) {
                System.err.println("Error while shuting down. " + exception);
            }
        }
    }

    private final Object _recoverLock = new Object();

    /**
     * Recover jmdns when there is an error.
     */
    public void recover() {
        logger.finer(this.getName() + "recover()");
        // We have an IO error so lets try to recover if anything happens lets close it.
        // This should cover the case of the IP address changing under our feet
        if (this.isClosing() || this.isClosed() || this.isCanceling() || this.isCanceled()) {
            return;
        }

        // We need some definite lock here as we may have multiple timer running in the same thread that will not be stopped by the reentrant lock
        // in the state object. This is only a problem in this case as we are going to execute in seperate thread so that the timer can clear.
        synchronized (this._recoverLock) {
            // Stop JmDNS
            // This protects against recursive calls
            if (this.cancelState()) {
                logger.finer(this.getName() + "recover() thread " + Thread.currentThread().getName());
                final Thread recover = new Thread(this.getName() + ".recover()") {
                    /**
                     * {@inheritDoc}
                     */
                    @Override
                    public void run() {
                        JmDNSImpl.this.__recover();
                    }
                };
                recover.start();
            }
        }
    }

    void __recover() {
        // Synchronize only if we are not already in process to prevent dead locks
        //
        if (logger.isLoggable(Level.FINER)) {
            logger.finer(this.getName() + "recover() Cleanning up");
        }

        logger.warning("RECOVERING");
        // Purge the timer
        this.purgeTimer();

        // We need to keep a copy for reregistration
        final Collection<ServiceInfo> oldServiceInfos = new ArrayList<ServiceInfo>(this.getServices().values());

        // Cancel all services
        this.unregisterAllServices();
        this.disposeServiceCollectors();

        this.waitForCanceled(DNSConstants.CLOSE_TIMEOUT);

        // Purge the canceler timer
        this.purgeStateTimer();

        //
        // close multicast socket
        this.closeMulticastSocket();

        //
        this.getCache().clear();
        if (logger.isLoggable(Level.FINER)) {
            logger.finer(this.getName() + "recover() All is clean");
        }

        if (this.isCanceled()) {
            //
            // All is clear now start the services
            //
            for (final ServiceInfo info : oldServiceInfos) {
                ((ServiceInfoImpl) info).recoverState();
            }
            this.recoverState();

            try {
                this.openMulticastSocket(this.getLocalHost());
                this.start(oldServiceInfos);
            } catch (final Exception exception) {
                logger.log(Level.WARNING, this.getName() + "recover() Start services exception ", exception);
            }
            logger.log(Level.WARNING, this.getName() + "recover() We are back!");
        } else {
            // We have a problem. We could not clear the state.
            logger.log(Level.WARNING, this.getName() + "recover() Could not recover we are Down!");
            if (this.getDelegate() != null) {
                this.getDelegate().cannotRecoverFromIOError(this.getDns(), oldServiceInfos);
            }
        }

    }

    public void cleanCache() {
        final long now = System.currentTimeMillis();
        for (final DNSEntry entry : this.getCache().allValues()) {
            try {
                final DNSRecord record = (DNSRecord) entry;
                if (record.isExpired(now)) {
                    this.updateRecord(now, record, Operation.Remove);
                    this.getCache().removeDNSEntry(record);
                } else if (record.isStale(now)) {
                    // we should query for the record we care about i.e. those in the service collectors
                    this.renewServiceCollector(record);
                }
            } catch (final Exception exception) {
                logger.log(Level.SEVERE, this.getName() + ".Error while reaping records: " + entry, exception);
                logger.severe(this.toString());
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void close() {
        if (this.isClosing()) {
            return;
        }

        if (logger.isLoggable(Level.FINER)) {
            logger.finer("Cancelling JmDNS: " + this);
        }
        // Stop JmDNS
        // This protects against recursive calls
        if (this.closeState()) {
            // We got the tie break now clean up

            // Stop the timer
            logger.finer("Canceling the timer");
            this.cancelTimer();

            // Cancel all services
            this.unregisterAllServices();
            this.disposeServiceCollectors();

            if (logger.isLoggable(Level.FINER)) {
                logger.finer("Wait for JmDNS cancel: " + this);
            }
            this.waitForCanceled(50);

            // Stop the canceler timer
            logger.finer("Canceling the state timer");
            this.cancelStateTimer();

            // Stop the executor
            this._executor.shutdown();

            // close socket
            this.closeMulticastSocket();

            // remove the shutdown hook
            if (this._shutdown != null) {
                Runtime.getRuntime().removeShutdownHook(this._shutdown);
            }

            if (logger.isLoggable(Level.FINER)) {
                logger.finer("JmDNS closed.");
            }
        }
        this.advanceState(null);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    @Deprecated
    public void printServices() {
        System.err.println(this.toString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder aLog = new StringBuilder(2048);
        aLog.append("\t---- Local Host -----");
        aLog.append("\n\t");
        aLog.append(this._localHost);
        aLog.append("\n\t---- Services -----");
        for (final String key : this._services.keySet()) {
            aLog.append("\n\t\tService: ");
            aLog.append(key);
            aLog.append(": ");
            aLog.append(this._services.get(key));
        }
        aLog.append("\n");
        aLog.append("\t---- Types ----");
        for (final String key : this._serviceTypes.keySet()) {
            final ServiceTypeEntry subtypes = this._serviceTypes.get(key);
            aLog.append("\n\t\tType: ");
            aLog.append(subtypes.getType());
            aLog.append(": ");
            aLog.append(subtypes.isEmpty() ? "no subtypes" : subtypes);
        }
        aLog.append("\n");
        aLog.append(this._cache.toString());
        aLog.append("\n");
        aLog.append("\t---- Service Collectors ----");
        for (final String key : this._serviceCollectors.keySet()) {
            aLog.append("\n\t\tService Collector: ");
            aLog.append(key);
            aLog.append(": ");
            aLog.append(this._serviceCollectors.get(key));
        }
        aLog.append("\n");
        aLog.append("\t---- Service Listeners ----");
        for (final String key : this._serviceListeners.keySet()) {
            aLog.append("\n\t\tService Listener: ");
            aLog.append(key);
            aLog.append(": ");
            aLog.append(this._serviceListeners.get(key));
        }
        return aLog.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ServiceInfo[] list(final String type) {
        return this.list(type, DNSConstants.SERVICE_INFO_TIMEOUT);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ServiceInfo[] list(final String type, final long timeout) {
        this.cleanCache();
        // Implementation note: The first time a list for a given type is
        // requested, a ServiceCollector is created which collects service
        // infos. This greatly speeds up the performance of subsequent calls
        // to this method. The caveats are, that 1) the first call to this
        // method for a given type is slow, and 2) we spawn a ServiceCollector
        // instance for each service type which increases network traffic a
        // little.

        final String loType = type.toLowerCase();

        boolean newCollectorCreated = false;
        if (this.isCanceling() || this.isCanceled()) {
            return new ServiceInfo[0];
        }

        ServiceCollector collector = this._serviceCollectors.get(loType);
        if (collector == null) {
            newCollectorCreated = this._serviceCollectors.putIfAbsent(loType, new ServiceCollector(type)) == null;
            collector = this._serviceCollectors.get(loType);
            if (newCollectorCreated) {
                this.addServiceListener(type, collector, ListenerStatus.SYNCHONEOUS);
            }
        }
        if (logger.isLoggable(Level.FINER)) {
            logger.finer(this.getName() + ".collector: " + collector);
        }
        // At this stage the collector should never be null but it keeps findbugs happy.
        return (collector != null ? collector.list(timeout) : new ServiceInfo[0]);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Map<String, ServiceInfo[]> listBySubtype(final String type) {
        return this.listBySubtype(type, DNSConstants.SERVICE_INFO_TIMEOUT);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Map<String, ServiceInfo[]> listBySubtype(final String type, final long timeout) {
        final Map<String, List<ServiceInfo>> map = new HashMap<String, List<ServiceInfo>>(5);
        for (final ServiceInfo info : this.list(type, timeout)) {
            final String subtype = info.getSubtype().toLowerCase();
            if (!map.containsKey(subtype)) {
                map.put(subtype, new ArrayList<ServiceInfo>(10));
            }
            map.get(subtype).add(info);
        }

        final Map<String, ServiceInfo[]> result = new HashMap<String, ServiceInfo[]>(map.size());
        for (final String subtype : map.keySet()) {
            final List<ServiceInfo> infoForSubType = map.get(subtype);
            result.put(subtype, infoForSubType.toArray(new ServiceInfo[infoForSubType.size()]));
        }

        return result;
    }

    /**
     * This method disposes all ServiceCollector instances which have been created by calls to method <code>list(type)</code>.
     * 
     * @see #list
     */
    private void disposeServiceCollectors() {
        if (logger.isLoggable(Level.FINER)) {
            logger.finer("disposeServiceCollectors()");
        }
        for (final String type : this._serviceCollectors.keySet()) {
            final ServiceCollector collector = this._serviceCollectors.get(type);
            if (collector != null) {
                this.removeServiceListener(type, collector);
                this._serviceCollectors.remove(type, collector);
            }
        }
    }

    /**
     * Instances of ServiceCollector are used internally to speed up the performance of method <code>list(type)</code>.
     * 
     * @see #list
     */
    private static class ServiceCollector implements ServiceListener {
        // private static Logger logger = Logger.getLogger(ServiceCollector.class.getName());

        /**
         * A set of collected service instance names.
         */
        private final ConcurrentMap<String, ServiceInfo>  _infos;

        /**
         * A set of collected service event waiting to be resolved.
         */
        private final ConcurrentMap<String, ServiceEvent> _events;

        /**
         * This is the type we are listening for (only used for debugging).
         */
        private final String                              _type;

        /**
         * This is used to force a wait on the first invocation of list.
         */
        private volatile boolean                          _needToWaitForInfos;

        public ServiceCollector(final String type) {
            super();
            this._infos = new ConcurrentHashMap<String, ServiceInfo>();
            this._events = new ConcurrentHashMap<String, ServiceEvent>();
            this._type = type;
            this._needToWaitForInfos = true;
        }

        /**
         * A service has been added.
         * 
         * @param event
         *            service event
         */
        @Override
        public void serviceAdded(final ServiceEvent event) {
            synchronized (this) {
                ServiceInfo info = event.getInfo();
                if ((info != null) && (info.hasData())) {
                    this._infos.put(event.getName(), info);
                } else {
                    final String subtype = (info != null ? info.getSubtype() : "");
                    info = ((JmDNSImpl) event.getDNS()).resolveServiceInfo(event.getType(), event.getName(), subtype, true);
                    if (info != null) {
                        this._infos.put(event.getName(), info);
                    } else {
                        this._events.put(event.getName(), event);
                    }
                }
            }
        }

        /**
         * A service has been removed.
         * 
         * @param event
         *            service event
         */
        @Override
        public void serviceRemoved(final ServiceEvent event) {
            synchronized (this) {
                this._infos.remove(event.getName());
                this._events.remove(event.getName());
            }
        }

        /**
         * A service has been resolved. Its details are now available in the ServiceInfo record.
         * 
         * @param event
         *            service event
         */
        @Override
        public void serviceResolved(final ServiceEvent event) {
            synchronized (this) {
                this._infos.put(event.getName(), event.getInfo());
                this._events.remove(event.getName());
            }
        }

        /**
         * Returns an array of all service infos which have been collected by this ServiceCollector.
         * 
         * @param timeout
         *            timeout if the info list is empty.
         * @return Service Info array
         */
        public ServiceInfo[] list(final long timeout) {
            if (this._infos.isEmpty() || !this._events.isEmpty() || this._needToWaitForInfos) {
                long loops = (timeout / 200L);
                if (loops < 1) {
                    loops = 1;
                }
                for (int i = 0; i < loops; i++) {
                    try {
                        Thread.sleep(200);
                    } catch (final InterruptedException e) {
                        /* Stub */
                    }
                    if (this._events.isEmpty() && !this._infos.isEmpty() && !this._needToWaitForInfos) {
                        break;
                    }
                }
            }
            this._needToWaitForInfos = false;
            return this._infos.values().toArray(new ServiceInfo[this._infos.size()]);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            final StringBuffer aLog = new StringBuffer();
            aLog.append("\n\tType: ");
            aLog.append(this._type);
            if (this._infos.isEmpty()) {
                aLog.append("\n\tNo services collected.");
            } else {
                aLog.append("\n\tServices");
                for (final String key : this._infos.keySet()) {
                    aLog.append("\n\t\tService: ");
                    aLog.append(key);
                    aLog.append(": ");
                    aLog.append(this._infos.get(key));
                }
            }
            if (this._events.isEmpty()) {
                aLog.append("\n\tNo event queued.");
            } else {
                aLog.append("\n\tEvents");
                for (final String key : this._events.keySet()) {
                    aLog.append("\n\t\tEvent: ");
                    aLog.append(key);
                    aLog.append(": ");
                    aLog.append(this._events.get(key));
                }
            }
            return aLog.toString();
        }
    }

    static String toUnqualifiedName(final String type, final String qualifiedName) {
        final String loType = type.toLowerCase();
        final String loQualifiedName = qualifiedName.toLowerCase();
        if (loQualifiedName.endsWith(loType) && !(loQualifiedName.equals(loType))) {
            return qualifiedName.substring(0, qualifiedName.length() - type.length() - 1);
        }
        return qualifiedName;
    }

    public Map<String, ServiceInfo> getServices() {
        return this._services;
    }

    public void setLastThrottleIncrement(final long lastThrottleIncrement) {
        this._lastThrottleIncrement = lastThrottleIncrement;
    }

    public long getLastThrottleIncrement() {
        return this._lastThrottleIncrement;
    }

    public void setThrottle(final int throttle) {
        this._throttle = throttle;
    }

    public int getThrottle() {
        return this._throttle;
    }

    public static Random getRandom() {
        return _random;
    }

    public void ioLock() {
        this._ioLock.lock();
    }

    public void ioUnlock() {
        this._ioLock.unlock();
    }

    public void setPlannedAnswer(final DNSIncoming plannedAnswer) {
        this._plannedAnswer = plannedAnswer;
    }

    public DNSIncoming getPlannedAnswer() {
        return this._plannedAnswer;
    }

    void setLocalHost(final HostInfo localHost) {
        this._localHost = localHost;
    }

    public Map<String, ServiceTypeEntry> getServiceTypes() {
        return this._serviceTypes;
    }

    public MulticastSocket getSocket() {
        return this._socket;
    }

    public InetAddress getGroup() {
        return this._group;
    }

    @Override
    public Delegate getDelegate() {
        return this._delegate;
    }

    @Override
    public Delegate setDelegate(final Delegate delegate) {
        final Delegate previous = this._delegate;
        this._delegate = delegate;
        return previous;
    }

}
