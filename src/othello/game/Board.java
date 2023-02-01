package othello.game;

import java.util.HashMap;
import java.util.Map;

/**
 * Board for the Othello game.
 */
public class Board {
    public static final String RESET = "\u001B[0m";

    public static final String BACKGROUND = "\u001B[41;1m";

    public static final int DIM = 8;
    private static final String DELIMITER = "    ";
    private static final String[] NUMBERING = {" 00 | 01 | 02 | 03 | 04 | 05 | 06 | 07 ", "----+----+----+----+----+----+----+----",
            " 08 | 09 | 10 | 11 | 12 | 13 | 14 | 15", "----+----+----+----+----+----+----+----", " 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 ", "----+----+----+----+----+----+----+----",
            " 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 ", "----+----+----+----+----+----+----+----", " 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39", "----+----+----+----+----+----+----+----",
            " 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 ", "----+----+----+----+----+----+----+----", " 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 ", "----+----+----+----+----+----+----+----",
            " 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 "};
    private static final String LINE = NUMBERING[1];

    private final Mark[][] fields;

    /**
     * Creates an empty board.
     */
    public Board() {
        this.fields = new Mark[DIM][DIM];
        for (int i = 0; i < DIM; i++) {
            for (int z = 0; z < DIM; z++) {
                fields[i][z] = Mark.EMPTY;
            }
        }
        this.setField(3, 3, Mark.WHITE);
        this.setField(4, 4, Mark.WHITE);
        this.setField(3, 4, Mark.BLACK);
        this.setField(4, 3, Mark.BLACK);
    }

    /**
     * Creates a deep copy of this field.
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < DIM*DIM); \result.fields[i] == this.fields[i]);
     @*/
    public Board deepCopy() {
        Board copy = new Board();
        for (int i = 0; i < DIM * DIM; i++) {
            int row = i / DIM;
            int col = i % DIM;
            copy.fields[row][col] = fields[row][col];
        }
        return copy;
    }


    /**
     * Returns true of the (row,col) pair refers to a valid field on the board.
     *
     * @return true if 0 <= row < DIM && 0 <= col < DIM >> ROW/COL are counted from 0</>
     */
    //@ ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
    public boolean isField(int row, int col) {
        return row >= 0 && row < DIM && col >= 0 && col < DIM;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     *
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field
     */
    /*@ requires isField(row, col);
    ensures \result == Mark.EMPTY || \result == Mark.BLACK || \result == Mark.WHITE;
     @*/
    public Mark getField(int row, int col) {
        return isField(row, col) ? fields[row][col] : null;
    }

    /**
     * Checks if field is empty
     *
     * @param row
     * @param col
     */
    /*@ensures getField(row, col) == Mark.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int row, int col) {
        return getField(row, col) == Mark.EMPTY;
    }

    /**
     * Tests if the whole board is full.
     *
     * @return true if all fields are occupied
     */
    /*@ ensures (\forall int i; (i >= 0 && i < DIM);
        (\forall int j; (j >= 0 && j < DIM); isEmptyField(i, j) == false));
    */
    public boolean isFull() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++)
                if (getField(i, j) == Mark.EMPTY) {
                    return false;
                }
        }
        return true;
    }

    /**
     * Checks if the piece has a upper-left piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the upper-left piece exists
     */
    public boolean HasLeftUpperDiagPiece(int row, int col, Mark m) {
        return getField(row - 1, col - 1) == m.other();
    }

    /**
     * Checks if the piece has a upper-right piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the upper-right piece exists
     */
    public boolean HasRightUpperDiagPiece(int row, int col, Mark m) {
        return getField(row - 1, col + 1) == m.other();
    }

    /**
     * Checks if the piece has a upper piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the upper piece exists
     */
    public boolean HasUpperPiece(int row, int col, Mark m) {
        return getField(row - 1, col) == m.other();
    }

    /**
     * Checks if the piece has a left piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the left piece exists
     */
    public boolean HasLeftPiece(int row, int col, Mark m) {
        return getField(row, col - 1) == m.other();
    }

    /**
     * Checks if the piece has a right piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the right piece exists
     */
    public boolean HasRightPiece(int row, int col, Mark m) {
        return getField(row, col + 1) == m.other();
    }

    /**
     * Checks if the piece has a lower-left piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the lower-left piece exists
     */
    public boolean HasLeftLowerDiagPiece(int row, int col, Mark m) {
        return getField(row + 1, col - 1) == m.other();
    }

    /**
     * Checks if the piece has a lower-right piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the lower-right piece exists
     */
    public boolean HasRightLowerDiagPiece(int row, int col, Mark m) {
        return getField(row + 1, col + 1) == m.other();
    }

    /**
     * Checks if the piece has a lower piece
     *
     * @param row the pieces row
     * @param col the pieces column
     * @param m   the pieces mark
     * @return if the lower piece exists
     */
    public boolean HasLowerPiece(int row, int col, Mark m) {
        return getField(row + 1, col) == m.other();
    }

    /**
     * Check if there's a winner and return it and if not return null
     *
     * @return the winner
     */
    public Mark getWinner() {
        Map<Mark, Integer> scores = currentScore();
        if (scores.get(Mark.BLACK) > scores.get(Mark.WHITE)) {
            return Mark.BLACK;
        } else if (scores.get(Mark.BLACK) < scores.get(Mark.WHITE)) {
            return Mark.WHITE;
        } else {
            return null;
        }
    }

    /**
     * Checks if the current score
     * By counting if it has more marks than the other color -> only happens if game is over
     *
     * @return true if the mark has won
     */
    /*@ ensures \result.get(Mark.BLACK) == (\sum int y; 0 <= y && y < DIM; ((\num_of int x; 0 <= x && x < DIM; getField(x,y) == Mark.BLACK)));
    ensures \result.get(Mark.WHITE) == (\sum int y; 0 <= y && y < DIM; ((\num_of int x; 0 <= x && x < DIM; getField(x,y) == Mark.WHITE)));
    @*/
    public Map<Mark, Integer> currentScore() {
        Map<Mark, Integer> score = new HashMap<>();
        int numBlack = 0;
        int numWhite = 0;
        score.put(Mark.BLACK, numBlack);
        score.put(Mark.WHITE, numWhite);
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                if (getField(row, col) == Mark.BLACK) {
                    numBlack += 1;
                    score.put(Mark.BLACK, numBlack);
                } else if (getField(row, col) == Mark.WHITE) {
                    numWhite += 1;
                    score.put(Mark.WHITE, numWhite);
                }
            }
        }
        return score;
    }

    /**
     * Compile and represent the board as a String with formatting and coloring
     *
     * @return board as a String
     */
    public String toString() {
        StringBuilder s = new StringBuilder();
        for (int i = 0; i < DIM; i++) {
            StringBuilder row = new StringBuilder();
            for (int j = 0; j < DIM; j++) {
                Mark field = getField(i, j);
                switch (field) {
                    case VALID -> {
                        int index = (DIM * i) + j;
                        if (index < 10) {
                            row.append(String.format(" 0%s ", index));
                        } else {
                            row.append(String.format(" %s ", index));
                        }
                    }
                    case BLACK -> row.append(" ⚫ " + BACKGROUND);
                    case WHITE -> row.append(" ⚪ " + BACKGROUND);
                    default -> row.append(DELIMITER + BACKGROUND);
                }
                if (j < DIM - 1) {
                    row.append("|" + BACKGROUND);
                }
            }
            s.append(BACKGROUND).append(row).append(RESET);
            if (i < DIM - 1) {
                s.append("\n" + BACKGROUND).append(LINE).append(RESET).append(DELIMITER).append("\n");
            }
        }
        return s.toString();
    }


    /**
     * Resets the board to its original state
     */
    public void reset() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                fields[i][j] = Mark.EMPTY;
            }
        }
        setField(3, 3, Mark.WHITE);
        setField(4, 4, Mark.WHITE);
        setField(3, 4, Mark.BLACK);
        setField(4, 3, Mark.BLACK);
    }

    /**
     * Sets the field to that mark
     *
     * @param row
     * @param col
     * @param m   mark
     */
    /*@ requires isField(row, col);
       ensures getField(row, col) == m;
     @*/
    public void setField(int row, int col, Mark m) {
        if (isField(row, col)) {
            fields[row][col] = m;
        }
    }
}
