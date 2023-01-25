package othello.game;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test for the OthelloGame and it's logic and behaviour
 */
public class GameTest {
    private TestPlayer player1; // BLACK
    private TestPlayer player2; // WHITE
    private OthelloGame game;

    @BeforeEach
    public void setUp() {
        player1 = new TestPlayer();
        player2 = new TestPlayer();
        game = new OthelloGame(player1, player2);

    }

    /**
     * Testing 100 random games.
     */
    @Test
    public void testFullRandomGame() {
        for (int i = 0; i < 100; i++) {
            setUp();
            while (!game.isGameOver()) {
                TestPlayer player = (TestPlayer) game.getTurn();
                List<Move> moves;
                int numberOfPieces = game.scores().get(Mark.BLACK) + game.scores().get(Mark.WHITE);
                int playerScore = game.scores().get(player.getMark());
                try {
                    moves = player.determineMove(game);
                    game.doMove(moves);
                    assertEquals(numberOfPieces + 1, game.scores().get(Mark.BLACK) + game.scores().get(Mark.WHITE));
                    assertTrue(game.scores().get(player.getMark()) >= playerScore + 2);
                } catch (NoValidMoves ignored) {
                    assertEquals(numberOfPieces, game.scores().get(Mark.BLACK) + game.scores().get(Mark.WHITE));
                }
                game.nextTurn();
            }
            if (game.scores().get(Mark.BLACK) > game.scores().get(Mark.WHITE)) {
                assertEquals(player1, game.getWinner());
            } else if (game.scores().get(Mark.BLACK) < game.scores().get(Mark.WHITE)) {
                assertEquals(player2, game.getWinner());
            } else {
                assertNull(game.getWinner());
            }
        }
    }


    /**
     * Test if the winner is black when black has the most pieces at the end of the game.
     */
    @Test
    public void testGetWinnerBlack() {
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                game.getBoard().setField(row, col, Mark.BLACK);
            }
        }

        assertEquals(game.getWinner(), player1);
    }

    /**
     * Test if the winner is white when white has the most pieces at the end of the game.
     */
    @Test
    public void testGetWinnerWhite() {
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                game.getBoard().setField(row, col, Mark.WHITE);
            }
        }
        assertEquals(game.getWinner(), player2);
    }


    /**
     * Tests all the valid moves for black at the start of the game.
     */
    @Test
    public void testEarlyGameValidMovesBlack() {
        List<Move> moves = game.getValidMoves(game.getTurn().getMark());

        //Marking the location of all valid moves on the board for BLACK(first turn) with the 'Valid' marker.
        for (Move m : moves) {
            game.getBoard().setField(m.getRow(), m.getCol(), Mark.VALID);
        }
        //Check if all these marked locations match up with a reference game of Othello.
        assertEquals(Mark.VALID, game.getBoard().getField(2, 3));
        assertEquals(Mark.VALID, game.getBoard().getField(3, 2));
        assertEquals(Mark.VALID, game.getBoard().getField(4, 5));
        assertEquals(Mark.VALID, game.getBoard().getField(5, 4));
    }


    /**
     * Tests all the valid moves for black from a predefined state.
     */
    @Test
    public void testGetValidMoves() {
        // Create scenario to check all the valid moves.
        game.getBoard().setField(2, 3, Mark.BLACK);
        game.getBoard().setField(3, 3, Mark.BLACK);
        game.getBoard().setField(4, 3, Mark.BLACK);

        game.getBoard().setField(4, 5, Mark.BLACK);

        game.getBoard().setField(2, 4, Mark.WHITE);
        game.getBoard().setField(3, 4, Mark.WHITE);
        game.getBoard().setField(4, 4, Mark.WHITE);
        game.getBoard().setField(5, 4, Mark.WHITE);

        //Marking the location of all valid moves on the board for BLACK(first turn) with the 'Valid' marker.
        List<Move> moves = game.getValidMoves(Mark.BLACK);
        for (Move m : moves) {
            game.getBoard().setField(m.getRow(), m.getCol(), Mark.VALID);
        }

        // getValidMoves makes a new move with a list of pieces to flip for each of the cardinal and ordinal directions
        // which means that for the same row and column, there might be multiple moves.
        assertEquals(6 + 1, moves.size());

        //Check if all these marked locations match up with a reference game of Othello.
        assertEquals(Mark.VALID, game.getBoard().getField(1, 5));
        assertEquals(Mark.VALID, game.getBoard().getField(2, 5));
        assertEquals(Mark.VALID, game.getBoard().getField(3, 5));
        assertEquals(Mark.VALID, game.getBoard().getField(5, 5));
        assertEquals(Mark.VALID, game.getBoard().getField(6, 5));
        assertEquals(Mark.VALID, game.getBoard().getField(6, 3));
    }

    /**
     * Tests if there are any valid moves on a full board.
     */
    @Test
    public void testValidMovesOnFullBoard() {
        // Fill in the board
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                game.getBoard().setField(row, col, Mark.BLACK);
            }
        }
        // Check no valid moves for both players
        assertTrue(game.getValidMoves(Mark.BLACK).isEmpty());
        assertTrue(game.getValidMoves(Mark.WHITE).isEmpty());
    }


    /**
     * Tests the number of discs both players have after an invalid move and after black playing a move at index 19.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testScoreEarlyGame() throws NoValidMoves {
        // Test with wrong move
        assertTrue(player1.constructMove(game, 2).isEmpty());
        // Test nothing changed
        assertEquals(2, game.getBoard().currentScore().get(player1.getMark()));
        assertEquals(2, game.getBoard().currentScore().get(player2.getMark()));
        // Test with correct move
        game.doMove(player1.constructMove(game, 19));
        // Test that changes are correct
        assertEquals(4, game.getBoard().currentScore().get(player1.getMark()));
        assertEquals(1, game.getBoard().currentScore().get(player2.getMark()));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the northern direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleUpperFlips() throws NoValidMoves {
        // Do the flip
        game.doMove(player1.constructMove(game, 19));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(2, 3));
        assertEquals(Mark.BLACK, game.getBoard().getField(3, 3));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the southern direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleLowerFlips() throws NoValidMoves {
        // Do the flip
        game.doMove(player1.constructMove(game, 44));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(4, 4));
        assertEquals(Mark.BLACK, game.getBoard().getField(5, 4));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the western direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleLeftFlips() throws NoValidMoves {
        // Do the flip
        game.doMove(player1.constructMove(game, 26));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(3, 3));
        assertEquals(Mark.BLACK, game.getBoard().getField(3, 2));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the eastern direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleRightFlips() throws NoValidMoves {
        // Do the flip
        game.doMove(player1.constructMove(game, 37));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(4, 4));
        assertEquals(Mark.BLACK, game.getBoard().getField(4, 5));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the north-western direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleUpperLeftDiagonalFlips() throws NoValidMoves {
        // Create scenario for flip to be possible
        game.doMove(player1.constructMove(game, 44));
        game.doMove(player2.constructMove(game, 43));
        // Do the flip
        game.doMove(player1.constructMove(game, 18));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(2, 2));
        assertEquals(Mark.BLACK, game.getBoard().getField(3, 3));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the north-eastern direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleUpperRightDiagonalFlips() throws NoValidMoves {
        // Create scenario for flip to be possible
        game.doMove(player1.constructMove(game, 19));
        game.doMove(player2.constructMove(game, 20));
        // Do the flip
        game.doMove(player1.constructMove(game, 13));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(2, 4));
        assertEquals(Mark.BLACK, game.getBoard().getField(1, 5));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the south-western direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleLowerLeftDiagonalFlips() throws NoValidMoves {
        // Create scenario for flip to be possible
        game.doMove(player1.constructMove(game, 44));
        game.doMove(player2.constructMove(game, 43));
        // Do the flip
        game.doMove(player1.constructMove(game, 50));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(6, 2));
        assertEquals(Mark.BLACK, game.getBoard().getField(5, 3));
    }

    /**
     * Tests if flipping a single piece and setting a piece in the south-eastern direction works correctly.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testSingleLowerRightDiagonalFlips() throws NoValidMoves {
        // Create scenario for flip to be possible
        game.doMove(player1.constructMove(game, 19));
        game.doMove(player2.constructMove(game, 20));
        // Do the flip
        game.doMove(player1.constructMove(game, 45));
        // Check if they are flipped
        assertEquals(Mark.BLACK, game.getBoard().getField(4, 4));
        assertEquals(Mark.BLACK, game.getBoard().getField(5, 5));
    }

    /**
     * Tests if playing a piece that affects multiple directions, correctly performs a single piece flip in the affected direction.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testMultiDirectionalSingleFlips() throws NoValidMoves {
        // Create scenario where playing a move affects multiple directions.
        game.getBoard().setField(2, 3, Mark.BLACK);
        game.getBoard().setField(3, 3, Mark.BLACK);
        game.getBoard().setField(4, 3, Mark.BLACK);
        game.getBoard().setField(4, 5, Mark.BLACK);
        game.getBoard().setField(2, 4, Mark.WHITE);
        game.getBoard().setField(3, 4, Mark.WHITE);
        game.getBoard().setField(4, 4, Mark.WHITE);
        game.getBoard().setField(5, 4, Mark.WHITE);
        // Do the flip
        game.doMove(player1.constructMove(game, 21));
        // Check if all pieces in the affected directions have been flipped.
        assertEquals(Mark.BLACK, game.getBoard().getField(2, 5));
        assertEquals(Mark.BLACK, game.getBoard().getField(2, 4));
        assertEquals(Mark.BLACK, game.getBoard().getField(3, 4));
    }

    /**
     * Tests if playing a piece that affects multiple directions, correctly performs multiple piece flips in the affected direction.
     *
     * @throws NoValidMoves exception for when the player has no valid moves to make
     */
    @Test
    public void testMultiDirectionalLongFlips() throws NoValidMoves {
        game.getBoard().setField(3, 2, Mark.BLACK);
        game.getBoard().setField(4, 2, Mark.BLACK);
        game.getBoard().setField(5, 2, Mark.BLACK);

        game.getBoard().setField(3, 3, Mark.BLACK);
        game.getBoard().setField(4, 3, Mark.BLACK);
        game.getBoard().setField(5, 3, Mark.BLACK);

        game.getBoard().setField(2, 4, Mark.WHITE);
        game.getBoard().setField(3, 4, Mark.BLACK);
        game.getBoard().setField(4, 4, Mark.BLACK);
        game.getBoard().setField(5, 4, Mark.BLACK);
        game.getBoard().setField(6, 4, Mark.BLACK);

        game.getBoard().setField(2, 5, Mark.BLACK);
        game.getBoard().setField(5, 5, Mark.WHITE);

        game.doMove(player2.constructMove(game, 41));
        assertEquals(Mark.WHITE, game.getBoard().getField(5, 5));
        assertEquals(Mark.WHITE, game.getBoard().getField(5, 4));
        assertEquals(Mark.WHITE, game.getBoard().getField(5, 3));
        assertEquals(Mark.WHITE, game.getBoard().getField(5, 2));
        assertEquals(Mark.WHITE, game.getBoard().getField(5, 1));
        assertEquals(Mark.WHITE, game.getBoard().getField(3, 3));
        assertEquals(Mark.WHITE, game.getBoard().getField(4, 2));
    }

    /**
     * Testing the game is over when
     * neither of the players can make a valid move
     */
    @Test
    public void testGameOverNoValidMovesBothPlayers() {
        // Creating a scenario where neither players have a valid move to make
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

    /**
     * Testing the game is over when there are no black pieces
     */
    @Test
    public void testGameOverNoBlacks() {
        // Removing all black pieces
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                if (game.getBoard().getField(row, col) == Mark.BLACK) {
                    game.getBoard().setField(row, col, Mark.WHITE);
                }
            }
        }
        assertTrue(game.isGameOver());
    }

    /**
     * Testing the game is over when there are no white pieces
     */
    @Test
    public void testGameOverNoWhites() {
        // Removing all white pieces
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                if (game.getBoard().getField(row, col) == Mark.WHITE) {
                    game.getBoard().setField(row, col, Mark.BLACK);
                }

            }
        }
        assertTrue(game.isGameOver());
    }

    /**
     * Testing the game is over when the board is full
     */
    @Test
    public void testGameOverBoardFull() {
        // Filling the board
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                game.getBoard().setField(row, col, Mark.BLACK);
            }
        }
        assertTrue(game.isGameOver());
    }
}
