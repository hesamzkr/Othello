package tictactoe.ui;

import tictactoe.ai.ComputerPlayer;
import tictactoe.ai.NaiveStrategy;
import tictactoe.ai.SmartStrategy;
import tictactoe.model.*;

import java.util.Scanner;

public class TicTacToeTUI {
    private TicTacToeGame game;

    private final AbstractPlayer player1;
    private final AbstractPlayer player2;

    public TicTacToeTUI(TicTacToeGame game, AbstractPlayer player1, AbstractPlayer player2) {
        this.game = game;
        this.player1 = player1;
        this.player2 = player2;
    }

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        System.out.print("Player1 name: ");
        AbstractPlayer player1 = createPlayer(scanner, Mark.XX);
        System.out.print("Player2 name: ");
        AbstractPlayer player2 = createPlayer(scanner, Mark.OO);

        TicTacToeTUI tui = new TicTacToeTUI(new TicTacToeGame(player1, player2), player1, player2);
        tui.run();
    }

    public void run() {
        boolean loop = true;
        while (loop) {
            while (!game.isGameover()) {
                System.out.printf("\n%s\n", game);
                AbstractPlayer player = (AbstractPlayer) game.getTurn();
                System.out.printf("\n%s (%s)%n", game.getTurn().toString(), game.getMark());
                Move move = player.determineMove(game);
                game.doMove(move);
                game.nextTurn();
            }
            System.out.printf("\n%s\n", game);
            Player winner = game.getWinner();
            if (winner != null) {
                System.out.printf("The winner is: %s!\n", winner);
            } else {
                System.out.println("The game is a draw!");
            }
            System.out.println("Do you want to continue? yes/no?");
            Scanner scan = new Scanner(System.in);
            String args = scan.nextLine();
            switch (args) {
                case "yes":
                    game = new TicTacToeGame(player1, player2);
                    break;
                case "no":
                    loop = false;
                    break;
                default:
                    System.out.println("Unknown command");
            }
        }
    }

    private static AbstractPlayer createPlayer(Scanner scanner, Mark mark) {
        String playerName = scanner.nextLine();
        switch (playerName) {
            case "-N":
                return new ComputerPlayer(mark, new NaiveStrategy());
            case "-S":
                return new ComputerPlayer(mark, new SmartStrategy());
            default:
                return new HumanPlayer(playerName);
        }
    }

}
