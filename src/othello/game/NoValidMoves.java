package othello.game;

public class NoValidMoves extends Exception {
    public NoValidMoves() {
        super("You have no valid moves to play.");
    }

}
