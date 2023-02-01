package othello.game;

import othello.ai.NaiveStrategy;
import othello.ai.Strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Player created for using in tests
 */
public class TestPlayer extends ComputerPlayer {

    public TestPlayer() {
        super("TEST PLAYER", new NaiveStrategy());
    }

    /**
     * Constructs a list of moves for testing when given
     * an index on the board as a move to make
     *
     * @param game      the current game being tested
     * @param moveIndex the move chosen by player
     * @return list of moves to be applied to game
     * @throws NoValidMoves Exception for when the player has no valid moves to make
     */
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
