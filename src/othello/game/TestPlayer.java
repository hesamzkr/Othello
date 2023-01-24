package othello.game;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Player created for using in tests
 */
public class TestPlayer extends ComputerPlayer {

    public TestPlayer() {
        super(new NaiveStrategy());
    }

    public List<Move> determineMove(Game game) throws NoValidMoves {
        return null;
    }

    public List<Move> constructMove(Game game, int moveIndex) throws NoValidMoves {
        List<Move> playMoves = new ArrayList<>();
        int row = moveIndex / Board.DIM;
        int col = moveIndex % Board.DIM;
        List<Move> moves = game.getValidMoves(super.mark);
        if (moves.isEmpty()) {
            throw new NoValidMoves();
        }
        for (Move m : moves) {
            if (m.getRow() == row && m.getCol() == col) {
                playMoves.add(m);
            }
        }
        if (!playMoves.isEmpty()) {
            return playMoves;
        } else {
            System.out.println("Invalid move entered.");
        }
        return playMoves;
    }
}
