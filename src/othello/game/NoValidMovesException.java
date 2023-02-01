package othello.game;

/**
 * Exception for when the player has no valid moves to make
 */
public class NoValidMovesException extends Exception {
    /**
     * Constructor of the exception with an exception constant message
     */
    public NoValidMovesException() {
        super("You have no valid moves to play");
    }
}
