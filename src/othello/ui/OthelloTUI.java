package othello.ui;

import othello.ai.Difficulty;
import othello.ai.MonteCarloStrategy;
import othello.ai.NaiveStrategy;
import othello.game.*;
import othello.game.AbstractPlayer;
import othello.game.Player;

import java.net.InetAddress;
import java.net.UnknownHostException;
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
        //Player p1 = new HumanPlayer(scanner.nextLine());
        Player p1 = createPlayer(scanner.nextLine());
        System.out.print("Player2 name: ");
        //Player p2 = new HumanPlayer(scanner.nextLine());
        Player p2 = createPlayer(scanner.nextLine());

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
                    if (game.getValidMoves(player.getMark()).isEmpty()) {
                        throw new NoValidMoves();
                    }
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
                Mark win = winner.getMark();
                Mark other = win.other();
                System.out.printf("The winner is: %s(%s)!, final score: %s vs %s \n", winner, winner.getMark(), game.scores().get(win), game.scores().get(win.other()));
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

    private static Player createPlayer(String name) {
        switch (name) {
            case "-N":
                return new ComputerPlayer(new NaiveStrategy());
//            case "-S":
//                return new ComputerPlayer(mark, new SmartStrategy());
            case "-M":
                return new ComputerPlayer(new MonteCarloStrategy(selectDifficulty(new Scanner(System.in))));
            default:
                return new HumanPlayer(name);
        }
    }

    private static Difficulty selectDifficulty(Scanner scanner) {
        System.out.println("Select a difficulty: easy, mid (medium), hard");
        String setting = scanner.nextLine();
        while (true) {
            switch (setting) {
                case "easy":
                    return Difficulty.EASY;
                case "mid":
                    return Difficulty.MEDIUM;
                case "hard":
                    return Difficulty.HARD;
                default:
                    System.out.println("Select a valid difficulty.");
            }
        }
    }

}
