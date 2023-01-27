package othello.client;

import othello.client.OthelloClient;
import othello.client.Client;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.InputMismatchException;
import java.util.Scanner;


public class OthelloApp {

    public static String filterString(Scanner scan) {
        while (true) {
            String text = scan.nextLine();
            if (text.equals("")) {
                continue;
            }
            return text;
        }
    }

    public static Integer filterInt(Scanner scan) {
        while (true) {
            Integer text = scan.nextInt();
            if (text.equals("")) {
                continue;
            }
            return text;
        }
    }

    public static void main(String[] args) {
        String address;
        int port;
        String username;
        ChatClient client;
        Scanner scan = new Scanner(System.in);
        Scanner scan2 = new Scanner(System.in);
        client = new MyChatClient();
        client.addChatListener(new MyChatListener());
        while (true) {
            try {
                System.out.println("Enter valid username.");
                username = scan.nextLine();
                if (username.contains("~")) {
                    throw new InvalidNameException("Enter a username without '~'.");
                }
                break;
            } catch (InvalidNameException e) {
                e.getMessage();
            }
        }
        while (true) {
            try {
                System.out.println("Enter a valid address.");
                //address = scan.nextLine();
                address = filterString(scan);
                scan.reset();
                System.out.println("Enter a valid port");
                //port = scan.nextInt();
                port = filterInt(scan);
//                if(!client.connect(InetAddress.getByName(address), port)) {
//                    throw new UnknownHostException();
//                }
                client.connect(InetAddress.getByName(address), port);
                System.out.printf("Connected to: %s %s\n", port, address);
                break;
            } catch (UnknownHostException | InputMismatchException e) {
                System.out.println(e.getMessage() + " Cannot connect to the server with the specified port.");
            }
        }
        try {
            client.sendUsername(username);
        } catch (NullPointerException e) {

        }
        Thread t1 = new Thread((MyChatClient) client);
        t1.start();
        while (true) {
            String msg = scan2.nextLine();
            //System.out.printf("%s",msg);
            if (msg.equals("quit")) {
                client.close();
                break;
            }
            client.sendMessage(msg);
            //write messages, check content locally on whether it is equal to quit
            // else do send message using the client.
        }
    }
}
