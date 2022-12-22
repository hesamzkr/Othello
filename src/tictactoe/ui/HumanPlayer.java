package tictactoe.ui;

import tictactoe.model.*;

import java.util.Scanner;

public class HumanPlayer extends AbstractPlayer {
    /**
     * Creates a new Player object.
     *
     * @param name
     */
    public HumanPlayer(String name) {
        super(name);
    }

    @Override
    public Move determineMove(Game game) {
        Scanner scan = new Scanner(System.in);
        TicTacToeGame newGame = (TicTacToeGame) game;
        Board board = newGame.getBoard();
        while (true) {
            System.out.print("Please enter a valid move: ");
            int index = scan.nextInt();
            int row = index / Board.DIM;
            int col = index % Board.DIM;
            Move newMove = new TicTacToeMove(newGame.getMark(), row, col);
            if (game.isValidMove(newMove)) {
                return newMove;
            } else {
                System.out.println("Invalid move, try again");
            }
        }
    }
}
