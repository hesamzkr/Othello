package othello.client;

import java.net.InetAddress;

/**
 * A client to be connected to a server with an address and port and handle sending messages
 */
public interface Client {

    /**
     * connects to the server
     *
     * @param address to connect to.
     * @param port    to connect to.
     */
    void connect(InetAddress address, int port);

    /**
     * closes the chat client
     */
    void close();


    /**
     * Sends a message to a client handler on the server.
     *
     * @param message
     */
    void send(String message);

}
