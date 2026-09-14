/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import VersoManual
import CedarDoc

open Verso.Genre Manual
open Verso.Output Html in

def main := manualMain (%doc CedarDoc) (config := {
  logo := some "static/cedar-logo.png",
  logoLink := none,
  sourceLink := some "https://github.com/cedar-policy/cedar-spec/tree/main/cedar-lean/Cedar/Thm",
  extraHead := #[{{
    <style>
      {{"
        .header-logo-wrapper {
          display: flex;
          align-items: center;
          gap: 0.75rem;
        }
        #logo { display: flex; align-items: center; }
        #logo img { height: 2rem; }
        #lean-logo { display: flex; align-items: center; }
        #lean-logo img { height: 1.8rem; }
        .header-title-wrapper {
          max-width: calc(100% - 28rem);
          overflow: hidden;
        }
        .header-title h1 {
          white-space: nowrap;
          overflow: hidden;
          text-overflow: ellipsis;
        }
        main .titlepage h1 {
          white-space: nowrap;
        }
        @media screen and (max-width: 700px) {
          header {
            display: flex !important;
            align-items: center !important;
          }
          .header-logo-wrapper {
            display: flex !important;
            order: 2;
            margin-left: auto;
            margin-right: 0.5rem;
          }
          #lean-logo img { height: 1.2rem; }
          #logo img { height: 1.5rem; }
          .header-title-wrapper {
            max-width: unset;
            overflow: visible;
            order: 1;
            text-align: center;
            flex: 1;
          }
          .header-title h1 {
            white-space: nowrap;
            font-size: 0.85rem;
            overflow: hidden;
            text-overflow: ellipsis;
          }
          main .titlepage h1 {
            white-space: normal;
          }
        }
      "}}
    </style>
  }}, {{
    <script>
      {{"
        document.addEventListener('DOMContentLoaded', function() {
          var wrapper = document.querySelector('.header-logo-wrapper');
          if (wrapper) {
            var cedarLogo = document.getElementById('logo');
            if (cedarLogo) cedarLogo.href = 'https://github.com/cedar-policy';
            var titleLink = document.querySelector('.header-title');
            if (titleLink) titleLink.href = document.querySelector('base').href;
            if (window.innerWidth <= 700) {
              var h1 = document.querySelector('.header-title h1');
              if (h1) h1.textContent = 'Cedar Extension Parsers';
            }
            var leanLink = document.createElement('a');
            leanLink.id = 'lean-logo';
            leanLink.href = 'https://github.com/cedar-policy/cedar-spec/tree/main/cedar-lean/Cedar/Thm';
            var img = document.createElement('img');
            img.src = 'static/lean-logo.svg';
            img.alt = 'Lean';
            leanLink.appendChild(img);
            wrapper.appendChild(leanLink);
          }
        });
      "}}
    </script>
  }}]
})
