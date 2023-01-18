package othello.game;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

public class BoardTest {
    private Board board;

    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    @Test
    public void testIndex() {
        for (int index = 0; index < Board.DIM * Board.DIM; index++) {
            int row = index / Board.DIM;
            int col = index % Board.DIM;
            assertTrue(board.isField(row, col));
        }
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
        board.setField(0, 1, Mark.BLACK);
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
}
