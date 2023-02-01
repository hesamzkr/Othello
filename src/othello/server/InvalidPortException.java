package othello.server;

/**
 * Exception for invalid port for the server
 */
public class InvalidPortException extends Exception {

    /**
     * Create instance of exception and pass message to parent
     */
    public InvalidPortException() {
        super("Invalid port entered");
    }

}
