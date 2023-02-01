package othello.game;

/**
 * Exception for when the player has no valid moves to make
 */
public class NoValidMoves extends Exception {
    /**
     * Constructor of the exception with a exceotion constant message
     */
    public NoValidMoves() {
        super("You have no valid moves to play");
    }
}
