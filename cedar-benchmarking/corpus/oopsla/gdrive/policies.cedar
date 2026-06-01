// If a user is granted view access to a document or a parent folder, or
// the enclosing group is granted view access, then they can read the
// document.
permit (
    principal,
    action == Action::"read",
    resource
)
when { resource in principal.documentsAndFoldersWithViewAccess };

// If a document is public, then anyone can read it.
permit (
    principal,
    action == Action::"read",
    resource
)
when { resource.isPublic };

// A document's owner (or owners of the parent folder) can read, write to,
// or share the document.
permit (
    principal,
    action in [Action::"read", Action::"write", Action::"share"],
    resource
)
when
{ resource in principal.ownedDocuments || resource in principal.ownedFolders };

// A document's owner can change the owner.
permit (
    principal,
    action == Action::"changeOwner",
    resource
)
when { principal.ownedDocuments.contains(resource) };

// A folder's owner can create documents.
permit (
    principal,
    action == Action::"createDocument",
    resource
)
when { principal.ownedFolders.contains(resource) };