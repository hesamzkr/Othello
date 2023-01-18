package othello;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import othello.game.Board;
import othello.game.Mark;

public class BoardTest {
    private Board board;

    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    @Test
    public void testIndex() {
        int index = 0;
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                assertEquals(index, board.index(i, j));
                index += 1;
            }
        }
//        assertEquals(0, board.index(0, 0));
//        assertEquals(1, board.index(0, 1));
//        assertEquals(3, board.index(1, 0));
//        assertEquals(8, board.index(2, 2));
    }

    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(Board.DIM * Board.DIM - 1));
        assertFalse(board.isField(Board.DIM * Board.DIM));
    }

    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(2, 2));
        assertFalse(board.isField(2, 3));
        assertFalse(board.isField(3, 2));
    }

    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Mark.BLACK);
        assertEquals(Mark.BLACK, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(1));
    }

    @Test
    public void testSetAndGetFieldRowCol() {
        board.setField(0, 0, Mark.BLACK);
        assertEquals(Mark.BLACK, board.getField(0, 0));
        assertEquals(Mark.EMPTY, board.getField(0, 1));
        assertEquals(Mark.EMPTY, board.getField(1, 0));
        assertEquals(Mark.EMPTY, board.getField(1, 1));
    }

    @Test
    public void testSetup() {
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            assertEquals(Mark.EMPTY, board.getField(i));
        }
//        assertEquals(Mark.EMPTY, board.getField(Board.DIM * Board.DIM - 1));
    }

    @Test
    public void testReset() {
        board.setField(0, Mark.BLACK);
        board.setField(Board.DIM * Board.DIM - 1, Mark.WHITE);
        board.reset();
        assertEquals(Mark.EMPTY, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(Board.DIM * Board.DIM - 1));
    }

    @Test
    public void testDeepCopy() {
        board.setField(0, Mark.BLACK);
        board.setField(Board.DIM * Board.DIM - 1, Mark.WHITE);
        Board deepCopyBoard = board.deepCopy();

        // First test if all the fields are the same
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            assertEquals(board.getField(i), deepCopyBoard.getField(i));
        }

        // Check if a field in the deepcopied board the original remains the same
        deepCopyBoard.setField(0, Mark.WHITE);

        assertEquals(Mark.BLACK, board.getField(0));
        assertEquals(Mark.WHITE, deepCopyBoard.getField(0));
    }

    @Test
    public void testIsEmptyFieldIndex() {
        board.setField(0, Mark.BLACK);
        assertFalse(board.isEmptyField(0));
        assertTrue(board.isEmptyField(1));
    }

    @Test
    public void testIsEmptyFieldRowCol() {
        board.setField(0, 0, Mark.BLACK);
        assertFalse(board.isEmptyField(0, 0));
        assertTrue(board.isEmptyField(0, 1));
        assertTrue(board.isEmptyField(1, 0));
    }

    @Test
    public void testIsFull() {
        for (int i = 0; i < Board.DIM * Board.DIM - 1; i++) {
            board.setField(i, Mark.BLACK);
        }
        assertFalse(board.isFull());

        board.setField(Board.DIM * Board.DIM - 1, Mark.BLACK);
        assertTrue(board.isFull());
    }

    @Test
    public void testGameOverAndHasNoWinnerFullBoard() {
        /**
         * xxo
         * oox
         * xxo
         */
        board.setField(0, 0, Mark.BLACK);
        board.setField(0, 1, Mark.BLACK);
        board.setField(0, 2, Mark.WHITE);
        board.setField(1, 0, Mark.WHITE);
        board.setField(1, 1, Mark.WHITE);
        board.setField(1, 2, Mark.BLACK);
        board.setField(2, 0, Mark.BLACK);
        board.setField(2, 1, Mark.WHITE);

        assertFalse(board.gameOver());
        assertFalse(board.hasWinner());
        board.setField(2, 2, Mark.BLACK);
        assertTrue(board.gameOver());
        assertFalse(board.hasWinner());
    }

    @Test
    public void testHasRow() {
        board.setField(0, Mark.BLACK);
        board.setField(1, Mark.BLACK);
        assertFalse(board.hasRow(Mark.BLACK));
        assertFalse(board.hasRow(Mark.WHITE));

        board.setField(2, Mark.BLACK);
        assertTrue(board.hasRow(Mark.BLACK));
        assertFalse(board.hasRow(Mark.WHITE));

        board.reset();

        board.setField(6, Mark.WHITE);
        board.setField(7, Mark.WHITE);
        assertFalse(board.hasRow(Mark.WHITE));
        assertFalse(board.hasRow(Mark.BLACK));

        board.setField(8, Mark.WHITE);
        assertTrue(board.hasRow(Mark.WHITE));
        assertFalse(board.hasRow(Mark.BLACK));
    }

    @Test
    public void testHasColumn() {
        board.setField(0, Mark.BLACK);
        board.setField(3, Mark.BLACK);
        assertFalse(board.hasColumn(Mark.BLACK));
        assertFalse(board.hasColumn(Mark.WHITE));

        board.setField(6, Mark.BLACK);
        assertTrue(board.hasColumn(Mark.BLACK));
        assertFalse(board.hasColumn(Mark.WHITE));

        board.reset();

        board.setField(2, Mark.WHITE);
        board.setField(5, Mark.WHITE);
        assertFalse(board.hasColumn(Mark.BLACK));
        assertFalse(board.hasColumn(Mark.WHITE));

        board.setField(8, Mark.WHITE);
        assertTrue(board.hasColumn(Mark.WHITE));
        assertFalse(board.hasColumn(Mark.BLACK));
    }

    @Test
    public void testHasDiagonalDown() {
        board.setField(0, 0, Mark.BLACK);
        board.setField(1, 1, Mark.BLACK);
        assertFalse(board.hasDiagonal(Mark.BLACK));
        assertFalse(board.hasDiagonal(Mark.WHITE));

        board.setField(2, 2, Mark.BLACK);
        assertTrue(board.hasDiagonal(Mark.BLACK));
        assertFalse(board.hasDiagonal(Mark.WHITE));
    }

    @Test
    public void testHasDiagonalUp() {
        board.setField(0, 2, Mark.BLACK);
        board.setField(1, 1, Mark.BLACK);
        assertFalse(board.hasDiagonal(Mark.BLACK));
        assertFalse(board.hasDiagonal(Mark.WHITE));

        board.setField(2, 0, Mark.BLACK);
        assertTrue(board.hasDiagonal(Mark.BLACK));
        assertFalse(board.hasDiagonal(Mark.WHITE));
    }

    @Test
    public void testIsWinner() {
        board.setField(0, Mark.BLACK);
        board.setField(1, Mark.BLACK);
        assertFalse(board.isWinner(Mark.BLACK));
        assertFalse(board.isWinner(Mark.WHITE));

        board.setField(2, Mark.BLACK);
        assertTrue(board.isWinner(Mark.BLACK));
        assertFalse(board.isWinner(Mark.WHITE));

        board.setField(0, 0, Mark.WHITE);
        board.setField(1, 1, Mark.WHITE);
        assertFalse(board.isWinner(Mark.BLACK));
        assertFalse(board.isWinner(Mark.WHITE));

        board.setField(2, 2, Mark.WHITE);
        assertFalse(board.isWinner(Mark.BLACK));
        assertTrue(board.isWinner(Mark.WHITE));
    }

    @Test
    public void testHasNoWinnerFullBoard() {
        /**
         * xxo
         * oox
         * xxo
         */
        board.setField(0, 0, Mark.BLACK);
        board.setField(0, 1, Mark.BLACK);
        board.setField(0, 2, Mark.WHITE);
        board.setField(1, 0, Mark.WHITE);
        board.setField(1, 1, Mark.WHITE);
        board.setField(1, 2, Mark.BLACK);
        board.setField(2, 0, Mark.BLACK);
        board.setField(2, 1, Mark.WHITE);
        board.setField(2, 2, Mark.BLACK);
        assertFalse(board.hasWinner());
    }

    @Test
    public void testHasWinnerRow() {
        board.setField(0, Mark.BLACK);
        board.setField(1, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(2, Mark.BLACK);
        assertTrue(board.hasWinner());

        board.reset();

        board.setField(3, Mark.BLACK);
        board.setField(4, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(5, Mark.BLACK);
        assertTrue(board.hasWinner());

        board.reset();

        board.setField(6, Mark.BLACK);
        board.setField(7, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(8, Mark.BLACK);
        assertTrue(board.hasWinner());
    }

    @Test
    public void testHasWinnerColumn() {
        board.setField(0, Mark.BLACK);
        board.setField(3, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(6, Mark.BLACK);
        assertTrue(board.hasWinner());

        board.reset();

        board.setField(1, Mark.BLACK);
        board.setField(4, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(7, Mark.BLACK);
        assertTrue(board.hasWinner());

        board.reset();

        board.setField(2, Mark.BLACK);
        board.setField(5, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(8, Mark.BLACK);
        assertTrue(board.hasWinner());
    }

    @Test
    public void testHasWinnerDiagonal() {
        board.setField(0, Mark.BLACK);
        board.setField(4, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(8, Mark.BLACK);
        assertTrue(board.hasWinner());

        board.reset();

        board.setField(2, Mark.BLACK);
        board.setField(4, Mark.BLACK);
        assertFalse(board.hasWinner());

        board.setField(6, Mark.BLACK);
        assertTrue(board.hasWinner());
    }
}
