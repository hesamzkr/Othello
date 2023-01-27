package othello.client;

import java.net.InetAddress;

public interface Client {

    /**
     * connects to the server
     *
     * @param address
     * @param port
     * @return whether it was successful or not
     */
    boolean connect(InetAddress address, int port);

    /**
     * closes the chat client
     */
    void close();


    /**
     * Sends a message to a client handler on the server.
     *
     * @param message
     * @return whether it was successful or not
     */
    boolean send(String message);

}
