# Build with pdfLaTeX, matching arXiv's AutoTeX engine.
#
# The Lean listings are kept as real UTF-8 source and rendered through the `listings`
# `literate` table.  That mechanism is driven by listings' own UTF-8 byte decoder,
# which is active under pdfLaTeX but bypassed under LuaLaTeX/XeLaTeX (they read UTF-8
# natively, so the glyphs would hit the monospace font and vanish).  Hence pdfLaTeX.
$pdf_mode = 1;
