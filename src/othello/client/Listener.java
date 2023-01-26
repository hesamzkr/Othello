package othello.client;

public interface Listener {
    /**
     * Show the message received on screen.
     *
     * @param from username
     * @param msg  message
     */
    void messageReceived(String from, String msg);
}
