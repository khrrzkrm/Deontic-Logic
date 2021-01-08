package de.uni_luebeck.isp.mockito;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

/**
 * Test suite using a mock class written manually.
 * 
 * @author Malte Schmitz (Institute for Software Engineering and Programming Languages, Universitaet zu Luebeck)
 *
 */
public class TestWithManualMockup {
	private ListenerMockup a, b;
	private Provider provider;
	
	@Before
	public void setUp() {
		a = new ListenerMockup();
		b = new ListenerMockup();
		
		provider = new Provider();
		provider.addListener(a);
		provider.addListener(b);
		provider.addListener(b);
		
		provider.notifyListeners("Two");
		provider.notifyListeners("One");
		provider.notifyListeners("Two");
	}
	
	@Test
	public void addTwice() {
		assertEquals("call(\"One\") should be called once.", 1, a.getCount("One"));
		assertEquals("call(\"Two\") should be called twice.", 2, a.getCount("Two"));
	}
	
	@Test
	public void addOnce() {
		assertEquals("call(\"One\") should be called twice.", 2, b.getCount("One"));
		assertEquals("call(\"Two\") should be called four times.", 4, b.getCount("Two"));
	}
}
