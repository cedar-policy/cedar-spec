/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

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
