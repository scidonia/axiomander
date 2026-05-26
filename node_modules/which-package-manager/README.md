# which-package-manager

Detects the current package manager. Rules applied in order:

- Lock file existence.
- `package.json` structure compatibility.
- `packageManager` field.
- First compatible passed preferred package manager.

## Usage

```sh
npm install which-package-manager
```

```js
import { whichPackageManager } from 'which-package-manager';

const packageManager = await whichPackageManager();
```

## License

MIT
