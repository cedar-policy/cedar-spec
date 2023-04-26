package com.CedarDefinitionalImplementation.log;
import java.util.function.Supplier;

public class Timer<T> implements Supplier<T> { 

	private final T result;
	private final long duration;

	public Timer(Supplier<T> s) { 
		long start = System.nanoTime();
		result = s.get();
		long end = System.nanoTime();
		duration = end - start;
	}

	public T get() { 
		return result;
	}

	public long getDuration() { 
		return duration;
	}
}



