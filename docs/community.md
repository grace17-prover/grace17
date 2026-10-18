# Community

Grace17 is open source and licensed under Apache 2.0. I am having a
fascinating time developing it and hope it is useful for your research. I
welcome contributors, both to the core system ecosystem and to Cumulus and
other mathematical libraries. Grace17 is still in an early stage, and I'd love
to have passionate collaborators join me in my dream to make set theoretic
formal mathematics mainstream.

## Zulip

The Grace17 community chats on Zulip at
[grace17.zulipchat.com](https://grace17.zulipchat.com). Zulip's topic-based
threads suit mathematics well: a question about one proof stays in one
thread, and a stream per subject keeps library discussions findable later.
Introduce yourself, ask how to prove something, show a development, or propose
a change to Cumulus.

## GitHub

The source, the issue tracker, and pull requests live at
[github.com/grace17-prover/grace17](https://github.com/grace17-prover/grace17).
Bug reports
with a small `.g17` file that reproduces the problem are the most useful kind.
Read [contributing](contributing.md) before a first pull request; it explains
the checks a change must pass and the conventions the library follows.

## Grace17 in Claude Code

If you work with Claude Code, install the Grace17 skill from inside it with
`/plugin install grace17 --marketplace grace17-prover/grace17`. The skill teaches an agent the write–check
loop, Cumulus conventions, and the pitfalls that cost the most time; the
[agents guide](agents.md) has the details and the other interfaces.

## Citing Grace17

If Grace17 or Cumulus plays a part in your work, please cite it:

```bibtex
@misc{passmore2026grace17,
  author = {Passmore, Grant Olney},
  title  = {The {Grace17} proof assistant for mathematics based on set theory},
  year   = {2026},
  url    = {https://grace17.org},
  note   = {Source code at \url{https://github.com/grace17-prover/grace17}}
}
```

The repository also carries this in `CITATION.cff`, which GitHub renders
under "Cite this repository".

## Contributing mathematics

Please contribute to Cumulus! The [Cumulus guide](cumulus.md) lists what exists, the
[Top 100](top-100.md) lists classical theorems still open, and
[build your own library](external-libraries.md) shows how to develop a
separate project against Cumulus before proposing it for inclusion.
