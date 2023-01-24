package othello.game;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

/**
 * Test for the board for othello
 */
public class BoardTest {
    private Board board;

    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    /**
     * Test all indices are on the board as a field with the
     * correct row and column
     */
    @Test
    public void testIndex() {
        for (int index = 0; index < Board.DIM * Board.DIM; index++) {
            int row = index / Board.DIM;
            int col = index % Board.DIM;
            assertTrue(board.isField(row, col));
        }
    }

    /**
     * Test the edge cases of rows and columns and
     * if they exist or not
     */
    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(2, 2));
        assertTrue(board.isField(Board.DIM - 1, Board.DIM - 1));
        assertFalse(board.isField(Board.DIM + 1, Board.DIM));
        assertFalse(board.isField(Board.DIM, Board.DIM + 1));
    }

    /**
     * Test if setting field works with rows and columns
     */
    @Test
    public void testSetAndGetFieldRowCol() {
        board.setField(0, 0, Mark.BLACK);
        assertEquals(Mark.BLACK, board.getField(0, 0));
        assertEquals(Mark.EMPTY, board.getField(0, 1));
        assertEquals(Mark.EMPTY, board.getField(1, 0));
        assertEquals(Mark.EMPTY, board.getField(1, 1));
    }

    /**
     * Test the initial state of the board
     */
    @Test
    public void testSetup() {
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            switch (i) {
                // indices for initial state
                case 27 -> assertEquals(Mark.WHITE, board.getField(3, 3));
                case 28 -> assertEquals(Mark.BLACK, board.getField(3, 4));
                case 35 -> assertEquals(Mark.BLACK, board.getField(4, 3));
                case 36 -> assertEquals(Mark.WHITE, board.getField(4, 4));
                // the rest must be empty
                default -> {
                    int row = i / Board.DIM;
                    int col = i % Board.DIM;
                    assertEquals(Mark.EMPTY, board.getField(row, col));
                }
            }
        }
    }

    /**
     * Tests if a board is correctly reset to its initial state.
     */
    @Test
    public void testReset() {
        board.setField(0, 0, Mark.BLACK);
        board.setField(Board.DIM - 1, Board.DIM - 1, Mark.WHITE);
        board.reset();

        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            switch (i) {
                // indices for initial state
                case 27 -> assertEquals(Mark.WHITE, board.getField(3, 3));
                case 28 -> assertEquals(Mark.BLACK, board.getField(3, 4));
                case 35 -> assertEquals(Mark.BLACK, board.getField(4, 3));
                case 36 -> assertEquals(Mark.WHITE, board.getField(4, 4));
                // the rest must be empty
                default -> {
                    int row = i / Board.DIM;
                    int col = i % Board.DIM;
                    assertEquals(Mark.EMPTY, board.getField(row, col));
                }
            }
        }
    }

    /**
     * Tests if a copy of the board can be created, where setting a field on one board
     * does not affect the other.
     */
    @Test
    public void testDeepCopy() {
        board.setField(0, 0, Mark.BLACK);
        board.setField(Board.DIM - 1, Board.DIM - 1, Mark.WHITE);
        Board deepCopyBoard = board.deepCopy();

        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            int row = i / Board.DIM;
            int col = i % Board.DIM;
            assertEquals(board.getField(row, col), deepCopyBoard.getField(row, col));
        }

        deepCopyBoard.setField(0, 0, Mark.WHITE);

        assertEquals(Mark.BLACK, board.getField(0, 0));
        assertEquals(Mark.WHITE, deepCopyBoard.getField(0, 0));
    }

    /**
     * Tests if fields on the boards are empty by using their row and column.
     */
    @Test
    public void testIsEmptyFieldRowCol() {
        board.setField(0, 0, Mark.BLACK);
        assertFalse(board.isEmptyField(0, 0));
        assertTrue(board.isEmptyField(0, 1));
        assertTrue(board.isEmptyField(1, 0));
    }

    /**
     * Tests if a board is full when all possible fields have been filled.
     */
    @Test
    public void testIsFull() {
        for (int i = 0; i < Board.DIM * Board.DIM - 1; i++) {
            int row = i / Board.DIM;
            int col = i % Board.DIM;
            board.setField(row, col, Mark.BLACK);
        }
        assertFalse(board.isFull());
        board.setField(Board.DIM - 1, Board.DIM - 1, Mark.BLACK);
        assertTrue(board.isFull());
    }
}
