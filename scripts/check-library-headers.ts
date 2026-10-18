import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
const required = ['-- Part of Cumulus, the Grace17 mathematics library.', '-- Copyright (c) 2026 Grant Passmore.', '-- Released under the Apache License 2.0. See LICENSE in the repository root.', '-- Authors: Grant Passmore'];
function files(root: string): string[] {
 return readdirSync(root,{withFileTypes:true}).flatMap(entry => entry.isDirectory() ? files(join(root,entry.name)) : entry.name.endsWith('.g17') ? [join(root,entry.name)] : []);
}
const paths=['lib/Grace/Cumulus.g17',...files('lib/Grace/Cumulus')];
const missing=paths.filter(file=>{
 const header=readFileSync(file,'utf8').split(/^module /m)[0]!;
 return required.some(line=>!header.includes(line));
});
if(missing.length) { console.error('Incomplete Cumulus headers:\n'+missing.join('\n')); process.exitCode=1; }
else console.log(`Full headers verified in ${paths.length} Cumulus files.`);
