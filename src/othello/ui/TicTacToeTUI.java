//package othello.ui;
//
//import othello.ai.*;
//import othello.game.*;
//import othello.game.AbstractPlayer;
//import othello.game.ComputerPlayer;
//import othello.game.Player;
//
//import java.util.Scanner;
//
//public class TicTacToeTUI {
//    private TicTacToeGame game;
//
//    private final AbstractPlayer player1;
//    private final AbstractPlayer player2;
//
//    public TicTacToeTUI(TicTacToeGame game, AbstractPlayer player1, AbstractPlayer player2) {
//        this.game = game;
//        this.player1 = player1;
//        this.player2 = player2;
//    }
//
//    public static void main(String[] args) {
//        Scanner scanner = new Scanner(System.in);
//        System.out.print("Player1 name: ");
//        AbstractPlayer player1 = createPlayer(scanner, Mark.BLACK);
//        System.out.print("Player2 name: ");
//        AbstractPlayer player2 = createPlayer(scanner, Mark.WHITE);
//
//        TicTacToeTUI tui = new TicTacToeTUI(new TicTacToeGame(player1, player2), player1, player2);
//        tui.run();
//    }
//
//    public void run() {
//        boolean loop = true;
//        while (loop) {
//            while (!game.isGameover()) {
//                System.out.printf("\n%s\n", game);
//                AbstractPlayer player = (AbstractPlayer) game.getTurn();
//                System.out.printf("\n%s (%s)%n", game.getTurn().toString(), game.getMark());
//                Move move = player.determineMove(game);
//                game.doMove(move);
//                game.nextTurn();
//            }
//            System.out.printf("\n%s\n", game);
//            Player winner = game.getWinner();
//            if (winner != null) {
//                System.out.printf("The winner is: %s!\n", winner);
//            } else {
//                System.out.println("The game is a draw!");
//            }
//            System.out.println("Do you want to continue? yes/no?");
//            Scanner scan = new Scanner(System.in);
//            String args = scan.nextLine();
//            switch (args) {
//                case "yes":
//                    game = new TicTacToeGame(player1, player2);
//                    break;
//                case "no":
//                    loop = false;
//                    break;
//                default:
//                    System.out.println("Unknown command");
//            }
//        }
//    }
//
//    private static AbstractPlayer createPlayer(Scanner scanner, Mark mark) {
//        String playerName = scanner.nextLine();
//        switch (playerName) {
//            case "-N":
//                return new ComputerPlayer(mark, new NaiveStrategy());
//            case "-S":
//                return new ComputerPlayer(mark, new SmartStrategy());
//            case "-M":
//                return new ComputerPlayer(mark, new MonteCarloStrategy(selectDifficulty(scanner)));
//            default:
//                return new HumanPlayer(playerName);
//        }
//    }
//
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
//
//}
