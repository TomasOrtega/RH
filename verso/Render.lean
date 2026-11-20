import VersoManual

open Verso Doc Genre Manual Output.Html

def archive : Part Manual where
  title := #[.text "RH proof browser"]
  titleString := "RH proof browser"
  metadata := none
  content := #[]
  subParts := #[]

def main : IO UInt32 :=
  manualMain archive (options := []) (config := {
    destination := "_out"
    emitHtmlSingle := .immediately
    features := {.search}
    extraFilesHtml := [("browser.css", "browser.css"), ("browser.js", "browser.js")]
    extraHead := #[
      {{<link rel="stylesheet" href="browser.css"/>}},
      {{<script src="browser.js" defer="defer"></script>}}
    ]
    extraContents := #[{{<div id="proof-browser" data-search-host="" aria-live="polite">
      <p>"Loading the Lean proof archive…"</p>
    </div>}}]
  })
