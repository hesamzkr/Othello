package othello.game;

//import othello.ai.Score;

import othello.ai.Score;

import java.util.*;
import java.util.stream.Collectors;

/**
 * A implementation of the Othello turn-based game.
 */
public class OthelloGame implements Game {

    private final Player player1;
    private final Player player2;
    private Board board;
    private Player turn;

    public OthelloGame(Player player1, Player player2) {
        this.player1 = player1;
        player1.setMark(Mark.BLACK);
        this.player2 = player2;
        player2.setMark(Mark.WHITE);
        board = new Board();
        turn = player1;
    }


    public boolean isGameOver() {
        Map<Mark, Integer> scores = board.currentScore();
        return (getValidMoves(Mark.BLACK).isEmpty() && getValidMoves(Mark.WHITE).isEmpty()) || board.isFull() || scores.get(Mark.BLACK) == 0 || scores.get(Mark.WHITE) == 0;
    }

    public Player getTurn() {
        return turn;
    }

    public Player getWinner() {
        if (board.getWinner() == Mark.BLACK) {
            return player1;
        } else if (board.getWinner() == Mark.WHITE) {
            return player2;
        } else {
            return null;
        }
    }

    public List<Move> getValidMoves(Mark m) {
        List<Move> validMoves = new ArrayList<>();

        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                if (board.getField(row, col) == m) {
                    if (board.HasLeftUpperDiagPiece(row, col, m)) {
                        validMoves.add(ScanUpperDiagLeft(m, row, col));
                    }
                    if (board.HasRightUpperDiagPiece(row, col, m)) {
                        validMoves.add(ScanUpperDiagRight(m, row, col));
                    }
                    if (board.HasUpperPiece(row, col, m)) {
                        validMoves.add(ScanUpper(m, row, col));
                    }
                    if (board.HasLeftPiece(row, col, m)) {
                        validMoves.add(ScanLeftPiece(m, row, col));
                    }
                    if (board.HasRightPiece(row, col, m)) {
                        validMoves.add(ScanRightPiece(m, row, col));
                    }
                    if (board.HasLeftLowerDiagPiece(row, col, m)) {
                        validMoves.add(ScanLowerDiagLeft(m, row, col));
                    }
                    if (board.HasLowerPiece(row, col, m)) {
                        validMoves.add(ScanLower(m, row, col));
                    }
                    if (board.HasRightLowerDiagPiece(row, col, m)) {
                        validMoves.add(ScanLowerDiagRight(m, row, col));
                    }
                }
            }
        }
        return validMoves.stream().filter(move -> move != null).collect(Collectors.toList());
    }

    /**
     * Should take a list of valid moves and filter out any duplicates by adding their toFlips together.
     *
     * @return
     */
    public List<Move> combineMoves() {
        List<Move> combinedMoves = new ArrayList<>();
        List<Move> moves = getValidMoves(turn.getMark());
        List<int[]> ints = showValids(moves);
        int size = showValids(moves).size();
        for (int[] rc : showValids(moves)) { // go through all row/col pairs
            List<Move> combine = new ArrayList<>(); //For moves with the same row/col
            for (Move m : moves) {
                if (m.getRow() == rc[0] && m.getCol() == rc[1]) { //this could be multiple moves, or a single move.
                    combine.add(m);
                }
            }
            if (combine.size() > 1) {
                Move main = combine.get(0); //Add all the toFlips to this 'main' move.
                for (int i = 1; i < combine.size(); i++) {
                    OthelloMove toAdd = (OthelloMove) combine.get(i);
                    ((OthelloMove) main).addToFlip(toAdd.getToFlip());
                }
                combinedMoves.add(main);
                continue;
            }
            combinedMoves.add(combine.get(0));
        }
        return combinedMoves; //should be a filtered list of moves.
    }

    /**
     * Finds all adjacent pieces in the north-western direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanUpperDiagLeft(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row - 1, col - 1));
        int checkRow = row - 2;
        int checkCol = col - 2;
        while (board.isField(checkRow, checkCol)) {
            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, checkRow, checkCol);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(checkRow, checkCol) == m.other()) {
                toFlip.add(new OthelloMove(m, checkRow, checkCol));
                checkRow -= 1;
                checkCol -= 1;
            } else {
                break;
            }
        }
        return null;
    }

    /**
     * Finds all adjacent pieces in the northern direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanUpper(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row - 1, col));
        int checkRow = row - 2;
        while (board.isField(checkRow, col)) {
            if (board.getField(checkRow, col) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, checkRow, col);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(checkRow, col) == m.other()) {
                toFlip.add(new OthelloMove(m, checkRow, col));
                checkRow -= 1;
            } else {
                break;
            }
        }
        return null;
    }

    /**
     * Finds all adjacent pieces in the north-eastern direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanUpperDiagRight(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row - 1, col + 1));
        int checkRow = row - 2;
        int checkCol = col + 2;
        while (board.isField(checkRow, checkCol)) {
            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, checkRow, checkCol);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(checkRow, checkCol) == m.other()) {
                toFlip.add(new OthelloMove(m, checkRow, checkCol));
                checkRow -= 1;
                checkCol += 1;
            } else {
                break;
            }
        }
        return null;
    }

    /**
     * Finds all adjacent pieces in the western direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanLeftPiece(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row, col - 1));
        int checkCol = col - 2;
        while (board.isField(row, checkCol)) {
            if (board.getField(row, checkCol) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, row, checkCol);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(row, checkCol) == m.other()) {
                toFlip.add(new OthelloMove(m, row, checkCol));
                checkCol -= 1;
            } else {
                break;
            }
        }
        return null;
    }

    /**
     * Finds all adjacent pieces in the eastern direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanRightPiece(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row, col + 1));
        int checkCol = col + 2;
        while (board.isField(row, checkCol)) {
            if (board.getField(row, checkCol) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, row, checkCol);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(row, checkCol) == m.other()) {
                toFlip.add(new OthelloMove(m, row, checkCol));
                checkCol += 1;
            } else {
                break;
            }
        }
        return null;
    }

    /**
     * Finds all adjacent pieces in the south-western direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanLowerDiagLeft(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row + 1, col - 1));
        int checkRow = row + 2;
        int checkCol = col - 2;
        while (board.isField(checkRow, checkCol)) {
            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, checkRow, checkCol);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(checkRow, checkCol) == m.other()) {
                toFlip.add(new OthelloMove(m, checkRow, checkCol));
                checkRow += 1;
                checkCol -= 1;
            } else {
                break;
            }
        }
        return null;
    }

    /**
     * Finds all adjacent pieces in the south-eastern direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanLowerDiagRight(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row + 1, col + 1));
        int checkRow = row + 2;
        int checkCol = col + 2;
        while (board.isField(checkRow, checkCol)) {
            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, checkRow, checkCol);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(checkRow, checkCol) == m.other()) {
                toFlip.add(new OthelloMove(m, checkRow, checkCol));
                checkRow += 1;
                checkCol += 1;
            } else {
                break;
            }
        }
        return null;
    }

    /**
     * Finds all adjacent pieces in the southern direction.
     *
     * @param m   the mark of the position from which the scan is performed.
     * @param row of the position from which the scan is performed.
     * @param col of the position from which the scan is performed.
     * @return a move which contains all the pieces that can be flipped.
     */
    public Move ScanLower(Mark m, int row, int col) {
        ArrayList<OthelloMove> toFlip = new ArrayList<>();
        toFlip.add(new OthelloMove(m, row + 1, col));
        int checkRow = row + 2;
        while (board.isField(checkRow, col)) {
            if (board.getField(checkRow, col) == Mark.EMPTY) {
                OthelloMove move = new OthelloMove(m, checkRow, col);
                move.addToFlip(toFlip);
                return move;
            } else if (board.getField(checkRow, col) == m.other()) {
                toFlip.add(new OthelloMove(m, checkRow, col));
                checkRow += 1;
            } else {
                break;
            }
        }
        return null;
    }


    public void doMove(List<Move> moves) {
        for (Move move : moves) {
            if (move instanceof OthelloMove othelloMove) {
                for (Move m : othelloMove.getToFlip()) {
                    doFlips(m);
                }
                doFlips(move);
            }
        }
    }

    public void doMove(int moveIndex) throws NoValidMoves {
        List<Move> playMoves = new ArrayList<>();
        int row = moveIndex / Board.DIM;
        int col = moveIndex % Board.DIM;
        List<Move> moves = getValidMoves(turn.getMark());
        if (moves.isEmpty()) {
            throw new NoValidMoves();
        }
        for (Move m : moves) {
            if (m.getRow() == row && m.getCol() == col) {
                playMoves.add(m);
            }
        }

        doMove(playMoves);
    }

    public Boolean isValidLocation(int row, int col) {
        return board.isEmptyField(row, col);
    }

    /**
     * Shows all the possible moves in a [row,column] format
     *
     * @return a list that only contains unique rows and columns.
     */
    public List<int[]> showValids(List<Move> moves) {
        //List<Move> moves = getValidMoves(getTurn().getMark());
        //Set<int[]> cache = new HashSet<>();
        List<int[]> valids = new ArrayList<>();
        for (Move m : moves) {
            int[] rowcol = new int[2];
            rowcol[0] = m.getRow();
            rowcol[1] = m.getCol();
            boolean contains = false;
            for (int[] l : valids) {
                if (l[0] == rowcol[0] && l[1] == rowcol[1]) {
                    contains = true;
                    break;
                }
            }
            if (!contains) {
                valids.add(rowcol);
            }
        }
        return valids; // NOT DOING THIS CORRECTLY
    }

    /**
     * should take a move and set it on the field, used when flipping and setting pieces.
     *
     * @param move the move to play
     */
    public void doFlips(Move move) {
        if (move instanceof OthelloMove othelloMove) {
            board.setField(othelloMove.getRow(), othelloMove.getCol(), othelloMove.getMark());
        }
    }

    public void nextTurn() {
        //turn = turn == player1 ? player2 : player1;
        if (turn == player1) {
            turn = player2;
        } else {
            turn = player1;
        }
    }

    public Board getBoard() {
        return board;
    }

    public void setBoard(Board board) {
        this.board = board;
    }

    public String toString() {
        List<Move> moves = getValidMoves(getTurn().getMark());
        Game copy = deepCopy();
        for (Move m : moves) {
            if (m instanceof OthelloMove othelloMove) {
                copy.getBoard().setField(othelloMove.getRow(), othelloMove.getCol(), Mark.VALID);
            }
        }
        return copy.getBoard().toString();
    }

    /**
     * Gives the scores for both players by their marks.
     *
     * @return a map with the scores for black and white.
     */
    public Map<Mark, Integer> scores() {
        return board.currentScore();
    }

    public OthelloGame deepCopy() {
        OthelloGame game = new OthelloGame(player1, player2);
        if (turn != player1)
            game.nextTurn();
        game.setBoard(board.deepCopy());
        return game;
    }

    public boolean isValidMove(int moveIndex) {
        int row = moveIndex / Board.DIM;
        int col = moveIndex % Board.DIM;
        List<Move> moves = getValidMoves(turn.getMark());
        for (Move m : moves) {
            if (m.getRow() == row && m.getCol() == col) {
                return true;
            }
        }
        return false;
    }


    /**
     * Maybe give this to AI because of modularity.
     *
     * @return
     */
    public Score getScores() {
        if (isGameOver()) {
            Player winner = getWinner();
            int bonus = 0;
            if (board.isFull() && winner != null) {
                if ((board.getField(0, 0) == winner.getMark()) && (board.getField(0, 7) == winner.getMark()) &&
                        (board.getField(7, 0) == winner.getMark()) && (board.getField(7, 7) == winner.getMark())) {
                    bonus += 0.0005;
                }
            }
            if (winner == player1) {
                return new Score(player1, player2, -1 + bonus, 1);
            } else if (winner == player2) {
                return new Score(player1, player2, 1, -1 + bonus);
            } else {
                return new Score(player1, player2, -0.5, -0.5);
            }
        }
        return null;
    }

    public Player getPlayer1() {
        return player1;
    }

    public Player getPlayer2() {
        return player2;
    }
}
