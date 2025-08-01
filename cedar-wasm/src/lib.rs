/*
 * Copyright Cedar Contributors
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
// src/lib.rs

#![allow(dead_code)]
use wasm_bindgen::prelude::*;
mod web_analysis;
mod web_cli_enums;
mod web_cli_exec;
mod web_err;
mod web_symcc;
mod web_util;

// Capture console output
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen]
pub async fn execute_command(command_type: &str, policyset_content: String, 
                            schema_content: String, tgt_policyset_content: Option<String>) 
                            -> Result<String, JsValue> {
    // Set up console error handling
    console_error_panic_hook::set_once();
    
    match command_type {
        "Analyze" => {        
            // Parse the files
            let policyset = web_util::parse_policyset_from_string(&policyset_content)
                .map_err(|e| JsValue::from_str(&format!("Error parsing policyset: {}", e)))?;
            let schema = web_util::parse_schema_from_string(&schema_content)
                .map_err(|e| JsValue::from_str(&format!("Error parsing schema: {}", e)))?;
            
            web_sys::console::log_2(&"Policy set: ".into(), &format!("{:?}", policyset).into());
            web_sys::console::log_2(&"Schema: ".into(), &format!("{:?}", schema).into());
            // Run analysis
            let result = web_analysis::analyze_policyset(policyset, schema)
                .await
                .map_err(|e| JsValue::from_str(&format!("Error analyzing policyset: {}", e)))?;
            Ok(result)
        },
        "Compare" => {
            // Ensure target policyset is provided
            let tgt_content = tgt_policyset_content.ok_or_else(|| 
                JsValue::from_str("Target policyset is required for Compare operation"))?;
            
            // Parse the files
            let src_policyset = web_util::parse_policyset_from_string(&policyset_content)
                .map_err(|e| JsValue::from_str(&format!("Error parsing source policyset: {}", e)))?;
            let tgt_policyset = web_util::parse_policyset_from_string(&tgt_content)
                .map_err(|e| JsValue::from_str(&format!("Error parsing target policyset: {}", e)))?;
            let schema = web_util::parse_schema_from_string(&schema_content)
                .map_err(|e| JsValue::from_str(&format!("Error parsing schema: {}", e)))?;
            
            // Run comparison
            let result = web_analysis::compare_policysets(src_policyset, tgt_policyset, schema)
                .await
                .map_err(|e| JsValue::from_str(&format!("Error comparing policysets: {}", e)))?;
            
            Ok(result)
        },
        _ => Err(JsValue::from_str(&format!("Unknown command type: {}", command_type)))
    }
}



