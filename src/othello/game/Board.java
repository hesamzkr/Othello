package othello.game;

import java.util.HashMap;
import java.util.Map;

/**
 * Board for the Tic Tac Toe game.
 */
public class Board {
    //DELETE
    /**
     * Dimension of the board, i.e., if set to 3, the board has 3 rows and 3 columns.
     */
    public static final String BLACK = "\u001B[30m";

    public static final String RESET = "\u001B[0m";

    public static final String GREEN_BACKGROUND = "\u001B[42m";

    public static final String RED = "\u001B[31m";
    public static final int DIM = 8;
    private static final String DELIM = "    ";
    private static final String[] NUMBERING = {" 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 ", "----+----+----+----+----+----+----+----",
            " 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15", "----+----+----+----+----+----+----+----", " 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 ", "----+----+----+----+----+----+----+----",
            " 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 ", "----+----+----+----+----+----+----+----", " 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39", "----+----+----+----+----+----+----+----",
            " 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 ", "----+----+----+----+----+----+----+----", " 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 ", "----+----+----+----+----+----+----+----",
            " 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 "};
    private static final String LINE = NUMBERING[1];

    /**
     * The DIM by DIM fields of the Tic Tac Toe board. See NUMBERING for the
     * coding of the fields.
     */
    private final Mark[][] fields;

    // -- Constructors -----------------------------------------------

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
     * checks left diagonal of a piece is possible
     * if there is an opposite mark there continue scanning
     * else return null
     *
     * @param row,col,m
     * @return
     */
    public boolean HasLeftUpperDiagPiece(int row, int col, Mark m) {
        return getField(row - 1, col - 1) == m.other();
    }

    /**
     * @param row
     * @param col
     * @param m
     * @return
     */
    public boolean HasRightUpperDiagPiece(int row, int col, Mark m) {
        return getField(row - 1, col + 1) == m.other();
    }

    /**
     * @param row
     * @param col
     * @param m
     * @return
     */
    public boolean HasUpperPiece(int row, int col, Mark m) {
        return getField(row - 1, col) == m.other();
    }

    /**
     * @param row
     * @param col
     * @param m
     * @return
     */
    public boolean HasLeftPiece(int row, int col, Mark m) {
        return getField(row, col - 1) == m.other();
    }

    /**
     * @param row
     * @param col
     * @param m
     * @return
     */
    public boolean HasRightPiece(int row, int col, Mark m) {
        return getField(row, col + 1) == m.other();
    }

    /**
     * @param row
     * @param col
     * @param m
     * @return
     */
    public boolean HasLeftLowerDiagPiece(int row, int col, Mark m) {
        return getField(row + 1, col - 1) == m.other();
    }

    /**
     * @param row
     * @param col
     * @param m
     * @return
     */
    public boolean HasRightLowerDiagPiece(int row, int col, Mark m) {
        return getField(row + 1, col + 1) == m.other();
    }

    public boolean HasLowerPiece(int row, int col, Mark m) {
        return getField(row + 1, col) == m.other();
    }

    /**
     * @return
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
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public String toString() {
        String s = "";
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                switch (getField(i, j)) {
                    case VALID:
                        int index = (DIM * i) + j;
                        row += " " + getField(i, j).toString().substring(0, 1).replace("V", RED + Integer.toString(index)) + " " + RESET + GREEN_BACKGROUND;
                        break;
                    case BLACK:
                        row += " " + getField(i, j).toString().substring(0, 1).replace("B", BLACK + "()" + RESET + GREEN_BACKGROUND) + " ";
                        break;
                    case WHITE:
                        row += " " + getField(i, j).toString().substring(0, 1).replace("W", "()") + " ";
                        break;
                    default:
                        row += " " + getField(i, j).toString().substring(0, 1).replace("E", "  ") + " ";
                }
//                if (getField(i, j) == Mark.VALID) {
//                    int index = (DIM * i) + j;
//                    row += " " + getField(i, j).toString().substring(0, 1).replace("V", Integer.toString(index)) + " ";
//                } else {
//                    row += " " + getField(i, j).toString().substring(0, 1).replace("E", " ") + " ";
//                }
                if (j < DIM - 1) {
                    row = GREEN_BACKGROUND + row + "|";
                }
            }
            s = GREEN_BACKGROUND + s + row + RESET + DELIM;
            if (i < DIM - 1) {
                s = s + "\n" + LINE + DELIM + "\n";
            }
        }
        return s;
    }


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

    public static void main(String[] args) {
        Board b = new Board();
        System.out.println(b.toString());
    }
}
