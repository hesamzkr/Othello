package othello.server;

import othello.server.InvalidPortException;

import java.util.Scanner;

public class OthelloServerApp {
    public static void main(String[] args) {
        OthelloServer server;
        int port;
        Scanner scan = new Scanner(System.in);
        Scanner scan2 = new Scanner(System.in);
        while (true) {
            try {
                System.out.println("Please enter a valid port number 0-65536");
                port = scan.nextInt();
                if (port < 0 || port > 65536) {
                    throw new InvalidPortException("Invalid port entered.");
                }
                server = new OthelloServer(port);
                server.start();
                System.out.printf("Created a server at: %s\n", port);
                break;
            } catch (InvalidPortException e) {
                e.getMessage();
            }
        }
        while (true) {
            String arg = scan2.nextLine();
            switch (arg) {
                case "quit":
                    server.stop();
                    break;
                case "port":
                    System.out.println(server.getPort());
                    continue;
                case "address":
                    System.out.println(server.getAddress());
                    continue;
                default:
                    if (arg != null) {
                        System.out.println("invalid command");
                    }
                    continue;
            }
            break;
        }
    }
}
