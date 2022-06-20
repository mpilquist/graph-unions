#!/bin/bash
cs launch org.scalameta:mdoc_3:2.3.2 -- --in README.template.md --out README.md --classpath $(cs fetch --classpath org.typelevel:cats-core_3:2.8.0) $*
