package othello.game;

import othello.ai.Score;

import java.util.ArrayList;
import java.util.List;

public class TicTacToeGame implements Game {

    private Player player1;
    private Player player2;
    private Board board;
    private Player turn;

    public TicTacToeGame(Player player1, Player player2) {
        this.player1 = player1;
        this.player2 = player2;
        turn = player1;
        this.board = new Board();
    }

    public boolean isGameover() {
        return board.gameOver();
    }

    public Player getTurn() {
        return turn;
    }

    public Mark getMark() {
        if (turn == player1) {
            return Mark.XX;
        } else {
            return Mark.OO;
        }
    }

    public Player getWinner() {
        if (board.hasWinner()) {
            if (board.isWinner(Mark.XX)) {
                return player1;
            } else if (board.isWinner(Mark.OO)) {
                return player2;
            }
        }
        return null;
    }

    public List<Move> getValidMoves() {
        List<Move> validMoves = new ArrayList<>();
        if (isGameover())
            return validMoves;

        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                if (board.isEmptyField(row, col)) {
                    Move move = new TicTacToeMove(getMark(), row, col);
                    validMoves.add(move);
                }
            }
        }

        return validMoves;
    }

    public boolean isValidMove(Move move) {
        TicTacToeMove newMove = (TicTacToeMove) move;
        if (board.isEmptyField(newMove.getRow(), newMove.getColumn())) {
            return turn == player1 && newMove.getMark() == Mark.XX || turn == player2 && newMove.getMark() == Mark.OO;
        }
        return false;
    }

    public void doMove(Move move) {
        if (move instanceof TicTacToeMove newMove) {
            board.setField(newMove.getRow(), newMove.getColumn(), newMove.getMark());
        }
    }

    public void nextTurn() {
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
        return board.toString();
    }

    public TicTacToeGame deepCopy() {
        TicTacToeGame game = new TicTacToeGame(player1, player2);
        if (turn != player1)
            game.nextTurn();
        game.setBoard(board.deepCopy());
        return game;
    }

    public Player getPlayer1() {
        return player1;
    }

    public Player getPlayer2() {
        return player2;
    }

    /**
     * requires the game to be over
     *
     * @return
     */
    public Score getScores() {
        if (isGameover()) {
            if (getWinner() == player1) {
                return new Score(player1, player2, 1, -2);
            } else if (getWinner() == player2) {
                return new Score(player1, player2, -2, 1);
            } else {
                return new Score(player1, player2, 0, 0);
            }
        }
        return null;
    }
}
