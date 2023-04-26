package com.CedarDefinitionalImplementation.log;

public enum LogTag { 
	Serialization,
	Deserialization,
	Auth,
	Validation;

	public String toString() { 
		switch (this) { 
			case Serialization:
				return "serialization_nanos";
			case Deserialization:
				return "deserialization_nanos";
			case Auth:
				return "auth_nanos";
			case Validation:
				return "validation_nanos";
		}
		throw new RuntimeException("Unreachable");
	}


	public static LogTag[] iter() { 
		LogTag[] arr = {LogTag.Serialization, LogTag.Deserialization, LogTag.Auth, LogTag.Validation};
		return arr;
	}

}
