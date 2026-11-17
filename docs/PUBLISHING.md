# GitHub publishing checklist

This package is **prepared for GitHub**, but cannot be uploaded until the repository owner connects a GitHub account or pushes from an authenticated computer.

1. Choose the repository owner/name (suggestion: `Absence-Spectrum`) and the intended visibility. No GitHub URL has yet been assigned.
2. This package includes the Apache License 2.0 in `LICENSE`. Before public release, confirm that the copyright holder(s) of the separately prepared `GW/` formalization authorize its distribution under Apache-2.0 (or retain its existing licensing terms and attributions). The original research papers are not relicensed.
3. Optionally inspect `README.md`, the two `verification/` files, and `docs/STATEMENT_GUIDE.md`. All original mathematical `.lean` files and locked dependency files are unchanged.
4. On a machine with Git and the GitHub CLI (`gh`) installed and authenticated, from **this directory**:

   ```sh
   git init -b main
   git add .
   git commit -m "Publish Lean formalization of the weak-coupling Fröhlich theorem"
   gh repo create OWNER/REPOSITORY --private --source=. --remote=origin --push
   ```

   Replace `OWNER/REPOSITORY` with the real account/name. `--private` is a safe first step; change visibility later once licensing and the public documentation have been reviewed. To publish publicly immediately, change `--private` to `--public`.
5. Open the GitHub Actions tab and check the first Lean verification job. It is not yet tested on GitHub. The job may take significant compute because the project contains hundreds of Lean modules.
6. Once the repository exists, replace the GitHub URL placeholder in the paper appendix and Section 1; keep the original manuscript untouched otherwise.

You can also create an empty repository through the GitHub website (without initializing a README or .gitignore) and use `git remote add origin https://github.com/OWNER/REPOSITORY.git; git push -u origin main` instead of `gh repo create`.
