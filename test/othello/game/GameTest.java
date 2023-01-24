package othello.game;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

public class GameTest {
    private TestPlayer player1; // BLACK
    private TestPlayer player2; // WHITE
    private OthelloGame game;

    @BeforeEach
    public void setUp() {
        player1 = new TestPlayer("Noah");
        player2 = new TestPlayer("Hesam");
        game = new OthelloGame(player1, player2);

    }

    @Test
    public void testEarlyGameValidMovesBlack() {
        List<Move> moves = game.getValidMoves(game.getTurn().getMark());
        Game copy = game.deepCopy();
        for (Move m : moves) {
            copy.getBoard().setField(m.getRow(), m.getCol(), Mark.VALID);
        }
        assertEquals(Mark.VALID, copy.getBoard().getField(2, 3));
        assertEquals(Mark.VALID, copy.getBoard().getField(3, 2));
        assertEquals(Mark.VALID, copy.getBoard().getField(4, 5));
        assertEquals(Mark.VALID, copy.getBoard().getField(5, 4));
    }

    @Test
    public void testNonAdjacentMoves() {

    }

    @Test
    public void testValidMoveNotOnPiece() {

    }

    @Test
    public void testMoveOnFullBoard() {

    }


    @Test
    public void testScoreEarlyGame() throws NoValidMoves {
        assertTrue(player1.constructMove(game, 2).isEmpty());
        game.doMove(player1.constructMove(game, 19));
        assertEquals(4, game.getBoard().currentScore().get(player1.getMark()));
        assertEquals(1, game.getBoard().currentScore().get(player2.getMark()));
    }

    @Test
    public void testSingleUpperFlips() throws NoValidMoves {
        game.doMove(player1.constructMove(game, 19));
        assertEquals(Mark.BLACK, game.getBoard().getField(2, 3));
        assertEquals(Mark.BLACK, game.getBoard().getField(3, 3));
        assertEquals(Mark.BLACK, game.getBoard().getField(4, 3));
    }

    @Test
    public void testSingleHorizontalFlips() throws NoValidMoves {
        //Left + right
    }

    @Test
    public void testSingleVerticalFlips() throws NoValidMoves {
        //up + down
    }

    @Test
    public void testSingleUpperDiagonalFlips() throws NoValidMoves {
        //diag left + right
    }

    @Test
    public void testSingleLowerDiagonalFlips() throws NoValidMoves {
        //diag left + right
    }

    @Test
    public void testMultiDirectionalSingleFlips() {

    }

    @Test
    public void testMultiDirectionalLongFlips() {

    }

    @Test
    public void testMostDiscsIsWinner() {

    }

    @Test
    public void testSameDiscsIsDraw() {

    }

    @Test
    public void testNoValidMovesForBothPlayers() {
        // No valid moves for either player
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                game.getBoard().setField(row, col, Mark.WHITE);
            }
        }

        for (int row = 0; row < Board.DIM - 1; row++) {
            game.getBoard().setField(row, 7, Mark.BLACK);
        }

        for (int col = 1; col < Board.DIM; col++) {
            game.getBoard().setField(0, col, Mark.BLACK);
        }

        game.getBoard().setField(0, 0, Mark.EMPTY);
        game.getBoard().setField(1, 0, Mark.EMPTY);
        game.getBoard().setField(7, 0, Mark.EMPTY);
        game.getBoard().setField(1, 6, Mark.EMPTY);
        game.getBoard().setField(7, 6, Mark.EMPTY);
        game.getBoard().setField(7, 7, Mark.EMPTY);

        assertTrue(game.isGameOver());
    }

    @Test
    public void testNoBlacks() {
        // No black pieces
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                if (game.getBoard().getField(row, col) == Mark.BLACK) {
                    game.getBoard().setField(row, col, Mark.WHITE);
                }
            }
        }
        assertTrue(game.isGameOver());
    }

    @Test
    public void testNoWhites() {
        // No white pieces
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                if (game.getBoard().getField(row, col) == Mark.WHITE) {
                    game.getBoard().setField(row, col, Mark.BLACK);
                }

            }
        }
        assertTrue(game.isGameOver());
    }

    @Test
    public void testBoardFull() {
        // Board is full
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                game.getBoard().setField(row, col, Mark.BLACK);
            }
        }
        assertTrue(game.isGameOver());
    }

    @Test
    public void testScoring() {

    }

    @Test
    public void testSkipIfNoValidMoves() {

    }

    @Test
    public void testGameOverNoValidMovesBothPlayers() {

    }
}
