'use strict';

const fs = require('node:fs');
const path = require('node:path');

const rootDir = path.resolve(__dirname, '..');
const readmeDir = path.join(rootDir, 'readmes');

for (const file of fs.readdirSync(readmeDir)) {
  if (!file.endsWith('.md')) continue;
  const target = path.basename(file, '.md');
  fs.copyFileSync(
    path.join(readmeDir, file),
    path.join(rootDir, 'npm', target, 'README.md'),
  );
}
