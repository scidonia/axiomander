"""Name resolution and uniquification for component compilation."""

from typing import List, Tuple, Dict, Set
from collections import defaultdict


class NameResolver:
    """Handles name uniquification to prevent import collisions."""
    
    def uniquify_names(self, uid_name_pairs: List[Tuple[str, str]]) -> List[str]:
        """Uniquify component names to prevent collisions.
        
        Args:
            uid_name_pairs: List of (uid, name) tuples
            
        Returns:
            List of uniquified names in the same order
        """
        # Group by name to find conflicts
        name_groups = defaultdict(list)
        for uid, name in uid_name_pairs:
            name_groups[name].append(uid)
        
        # Create uniquified names
        uniquified = {}
        
        for name, uids in name_groups.items():
            if len(uids) == 1:
                # No conflict, use original name
                uniquified[uids[0]] = name
            else:
                # Conflict, need to uniquify
                for uid in uids:
                    uniquified[uid] = self._create_unique_name(name, uid, uniquified.values())
        
        # Return in original order
        return [uniquified[uid] for uid, _ in uid_name_pairs]
    
    def _create_unique_name(self, base_name: str, uid: str, existing_names: Set[str]) -> str:
        """Create a unique name for a component with conflicts.
        
        Args:
            base_name: Original component name
            uid: Component UID
            existing_names: Set of already assigned names
            
        Returns:
            Uniquified name
        """
        # Try with first 8 characters of UID
        short_uid = uid.replace("-", "")[:8]
        candidate = f"{base_name}_{short_uid}"
        
        if candidate not in existing_names:
            return candidate
        
        # Try with full UID (remove dashes)
        full_uid = uid.replace("-", "")
        candidate = f"{base_name}_{full_uid}"
        
        if candidate not in existing_names:
            return candidate
        
        # Last resort: add counter
        counter = 1
        while True:
            candidate = f"{base_name}_{full_uid}_{counter}"
            if candidate not in existing_names:
                return candidate
            counter += 1
