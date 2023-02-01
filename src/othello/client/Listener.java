package othello.client;

/**
 * A listener for a client which will output messages depending on the UI it is designed for
 */
public interface Listener {

    /**
     * Print the message on to the UI the listener is designed for
     *
     * @param message to be printed
     */
    void print(String message);
}
