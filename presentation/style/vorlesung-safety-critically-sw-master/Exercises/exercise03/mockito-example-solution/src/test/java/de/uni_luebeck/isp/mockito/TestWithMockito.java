package de.uni_luebeck.isp.mockito;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;

import org.junit.Before;
import org.junit.Test;

/**
 * Test suite using Mockito to generate mock objects.
 * 
 * @author Malte Schmitz (Institute for Software Engineering and Programming
 *         Languages, Universitaet zu Luebeck)
 *
 */
public class TestWithMockito {
	private Listener a, b;
	private Provider provider;

	@Before
	public void setUp() {
		a = mock(Listener.class);
		b = mock(Listener.class);

		provider = new Provider();
		provider.addListener(a);
		provider.addListener(b);
		provider.addListener(b);

		provider.notifyListeners("Two");
		provider.notifyListeners("One");
		provider.notifyListeners("Two");
	}

	@Test
	public void addOnce() {
		verify(a).notify("One");
		verify(a, times(2)).notify("Two");
	}

	@Test
	public void addTwice() {
		verify(b, times(2)).notify("One");
		verify(b, times(4)).notify("Two");
	}
}
