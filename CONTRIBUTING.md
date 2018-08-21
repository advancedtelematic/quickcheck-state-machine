## Contributing

### Release checklist

  1. Update CHANGELOG.md;
  2. Bump version in .cabal file and fix bounds;
  3. Make tarball with `stack sdist --pvp-bounds lower`;
  4. Upload tarball as a
     package
     [candidate](https://hackage.haskell.org/packages/candidates/upload), and if
     everything looks good then release it;
  5. Git tag the version: `git tag -a v$VERSION -m "Tag v$VERISON" && git push
     origin v$VERSION`.
