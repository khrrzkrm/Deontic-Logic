package de.uni_luebeck.isp.mockito;

import java.util.HashMap;
import java.util.Map;

/**
 * Mock class for the {@link Listener} interface.
 * 
 * @author Malte Schmitz (Institute for Software Engineering and Programming
 *         Languages, Universitaet zu Luebeck)
 *
 */
public class ListenerMockup implements Listener {

  private Map<Object, Integer> counter = new HashMap<Object, Integer>();

  @Override
  public void notify(Object argument) {
    if (counter.containsKey(argument)) {
      int value = counter.get(argument);
      value += 1;
      counter.put(argument, value);
    } else {
      counter.put(argument, 1);
    }
  }

  public int getCount(Object argument) {
    if (counter.containsKey(argument)) {
      return counter.get(argument);
    } else {
      return 0;
    }
  }

}
