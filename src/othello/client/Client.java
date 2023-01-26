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
     * sends username to a client handler on the server.
     *
     * @param username of the chat
     * @return whether it was successful or not
     */
    boolean sendUsername(String username);

    /**
     * Sends a message to a client handler on the server.
     *
     * @param message
     * @return whether it was successful or not
     */
    boolean sendMessage(String message);

    /**
     * adds a chat listener to the client.
     *
     * @param listener
     */
    void addChatListener(Listener listener);

    /**
     * removes a chat listener from the client.
     *
     * @param listener
     */
    void removeChatListener(Listener listener);
}
