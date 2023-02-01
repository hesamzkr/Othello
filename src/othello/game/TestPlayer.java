package othello.game;

import othello.ai.NaiveStrategy;

import java.util.ArrayList;
import java.util.List;

/**
 * Player created for using in tests
 */
public class TestPlayer extends ComputerPlayer {

    /**
     * Constructor which sets the name and a strategy however neither of these are important for the TestPlayer
     */
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
     * @throws NoValidMovesException Exception for when the player has no valid moves to make
     */
    public List<Move> constructMove(Game game, int moveIndex) throws NoValidMovesException {
        List<Move> playMoves = new ArrayList<>();
        int row = moveIndex / Board.DIM;
        int col = moveIndex % Board.DIM;
        List<Move> moves = game.getValidMoves(super.mark);
        if (moves.isEmpty()) {
            throw new NoValidMovesException();
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
