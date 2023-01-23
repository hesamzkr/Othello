package othello.ui;

import othello.game.*;
import othello.game.AbstractPlayer;
import othello.game.Player;

import java.util.List;
import java.util.Scanner;

public class OthelloTUI {
    private OthelloGame game;

    public OthelloTUI(OthelloGame game) {
        this.game = game;
    }

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        System.out.print("Player1 name: ");
        Player p1 = new HumanPlayer(scanner.nextLine());
        //AbstractPlayer player1 = createPlayer(scanner, Mark.BLACK);
        System.out.print("Player2 name: ");
        Player p2 = new HumanPlayer(scanner.nextLine());
        //AbstractPlayer player2 = createPlayer(scanner, Mark.WHITE);

        OthelloTUI tui = new OthelloTUI(new OthelloGame(p1, p2));
        tui.run();
    }

    public void run() {
        boolean loop = true;
        while (loop) {
            while (!game.isGameOver()) {
                System.out.println(game);
                Player player = game.getTurn();
                System.out.printf("\n%s (%s)%n", game.getTurn().toString(), game.getTurn().getMark());
                List<Move> moves = null;
                try {
                    moves = player.determineMove(game);
                    game.doMove(moves);
                } catch (NoValidMoves e) {
                    System.out.printf("%s%n", e.getMessage());
                }
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
                    Player current = game.getTurn();
                    game.nextTurn();
                    Player next = game.getTurn();
                    game = new OthelloGame(current, next);
                    break;
                case "no":
                    loop = false;
                    break;
                default:
                    System.out.println("Unknown command");
            }
        }
    }

    private static Player createPlayer(Scanner scanner, Mark mark) {
        String playerName = scanner.nextLine();
        switch (playerName) {
//            case "-N":
//                return new ComputerPlayer(mark, new NaiveStrategy());
//            case "-S":
//                return new ComputerPlayer(mark, new SmartStrategy());
//            case "-M":
//                return new ComputerPlayer(mark, new MonteCarloStrategy(selectDifficulty(scanner)));
            default:
                return new HumanPlayer(playerName);
        }
    }

//    private static Difficulty selectDifficulty(Scanner scanner) {
//        System.out.println("Select a difficulty: easy, mid (medium), hard");
//        String setting = scanner.nextLine();
//        while (true) {
//            switch (setting) {
//                case "easy":
//                    return Difficulty.EASY;
//                case "mid":
//                    return Difficulty.MEDIUM;
//                case "hard":
//                    return Difficulty.HARD;
//                default:
//                    System.out.println("Select a valid difficulty.");
//            }
//        }
//    }

}
