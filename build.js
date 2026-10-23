'use strict';
const fs = require('fs');
const path = require('path');

const root = __dirname;
const template = fs.readFileSync(path.join(root, 'src', 'index.html'), 'utf8');
const app = fs.readFileSync(path.join(root, 'src', 'app.js'), 'utf8');
const peer = fs.readFileSync(path.join(root, 'vendor', 'peerjs.min.js'), 'utf8');

if (app.includes('</script>')) throw new Error('app.js contains a closing script tag');
if (peer.includes('</script>')) throw new Error('peerjs.min.js contains a closing script tag');
if (!template.includes('/*__PEERJS__*/') || !template.includes('/*__APP__*/')) {
  throw new Error('template placeholders missing');
}

const license = `/*!
 * PeerJS 1.5.5 | Copyright (c) 2015 Michelle Bu and Eric Zhang
 * Released under the MIT License | https://peerjs.com
 */
`;
const html = template
  .replace('/*__PEERJS__*/', () => license + peer)
  .replace('/*__APP__*/', () => app);

fs.writeFileSync(path.join(root, 'index.html'), html, 'utf8');
console.log(`Built index.html (${(Buffer.byteLength(html) / 1024).toFixed(1)} KiB)`);
