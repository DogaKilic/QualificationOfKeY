package util;

public class RandomGen2 {
    private int max, last;

    public RandomGen2(int max) {
        this.max = max;
        last = (int) (System.currentTimeMillis() % max);
    }

    public int nextInt() {
        last = (last * 32719 + 3) % 32749;
        return last % max;
    }
}
