package othello.game;

/**
 * Exception for when the player has no valid moves to make
 */
public class NoValidMoves extends Exception {
    public NoValidMoves() {
        super("You have no valid moves to play");
    }
}
