package othello.game;

import othello.ai.Score;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class OthelloGame implements Game {

    private final Player player1;
    private final Player player2;
    private Board board;
    private Player turn;

    public OthelloGame(Player player1, Player player2) {
        player1.setMark(Mark.BLACK);
        this.player1 = player1;
        player2.setMark(Mark.WHITE);
        this.player2 = player2;
        this.board = new Board();
    }

    public boolean isGameOver() {
        Map<Mark, Integer> scores = board.currentScore();
        return board.isFull() || scores.get(Mark.BLACK) == 0 || scores.get(Mark.WHITE) == 0;
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

    /**
     * has to check if a move is flippable
     * check if there is a similar mark closeby
     * check row, check column, check diagonal
     *
     * @return
     */
    public List<Move> getValidMoves(Mark m) {
        List<Move> validMoves = new ArrayList<>();
        if (isGameOver())
            return validMoves;

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
     * requires that HasUpperDiagLeft is true and only run in that case
     * checks next, next piece from the current location
     *
     * @return
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
     * Using setfield is supposed to take the location of a mark (from for loop)
     * and then the new move (has the mark of the player) is linked to that move
     * which allows the game to find where that mark is.
     *
     * @param m
     * @param row
     * @param col
     * @return
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
                toFlip.add(new OthelloMove(m, row, checkRow));
                checkRow -= 1;
            } else {
                break;
            }
        }
        return null;
    }

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
                toFlip.add(new OthelloMove(m, row, col));
                checkCol -= 1;
            } else {
                break;
            }
        }
        return null;
    }


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
                toFlip.add(new OthelloMove(m, row, checkRow));
                checkRow += 1;
            } else {
                break;
            }
        }
        return null;
    }

    public void doMove(Move move) {
        if (move instanceof OthelloMove othelloMove) {
            for (Move m : othelloMove.getToFlip()) {
                doFlips(m);
            }
            doFlips(move);
        }
    }

    /**
     * should take a move and flip all the pieces
     *
     * @param move the move to play
     */
    public void doFlips(Move move) {
        if (move instanceof OthelloMove othelloMove) {
            board.setField(othelloMove.getRow(), othelloMove.getRow(), othelloMove.getMark());
        }
    }

    public void nextTurn() {
        turn = turn == player1 ? player2 : player1;
    }

    public Board getBoard() {
        return board;
    }

    public void setBoard(Board board) {
        this.board = board;
    }

    public String toString() {
        return board.toString();
    }

    public OthelloGame deepCopy() {
        OthelloGame game = new OthelloGame(player1, player2);
        if (turn != player1)
            game.nextTurn();
        game.setBoard(board.deepCopy());
        return game;
    }

    public Score getScores() {
        if (isGameOver()) {
            Player winner = getWinner();
            if (winner == player1) {
                return new Score(player1, player2, 1, -2);
            } else if (winner == player2) {
                return new Score(player1, player2, -2, 1);
            } else {
                return new Score(player1, player2, 0, 0);
            }
        }
        return null;
    }
}
