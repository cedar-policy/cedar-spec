// Anyone can create a document or an image
@id("any-create")
permit (
    principal,
    action in [App::Action::"CreateDocument"],
    resource
);

// A User can perform any action on a File they own
@id("any-own")
permit (
    principal,
    action,
    resource is App::Document
)
when { resource.owner == principal };

// A User can Download a File is they are either owners, readers or editors
@id("download-file")
permit (
    principal,
    action == App::Action::"DownloadFile",
    resource is App::Document
)
when
{
    principal in resource.readers ||
    principal in resource.editors ||
    principal == resource.owner
};

// A User can edit a file if they are the owner or an editor
@id("edit-file")
permit (
    principal,
    action in [App::Action::"EditFile", App::Action::"AddReader"],
    resource is App::Document
)
when { principal in resource.editors };

// Admin can create Groups and users
@id("admin-create")
permit (
    principal in App::Group::"admin",
    action in [App::Action::"CreateGroup", App::Action::"CreateUser"],
    resource
);

// Admin can delete users under certain conditions
@id("admin-delete")
permit (
    principal in App::Group::"admin",
    action in [App::Action::"DeleteUser"],
    resource is App::User
) when {
    resource.jobLevel <= principal.jobLevel
};

// Security Group can view critical documents.
@id("sec-view")
permit (
    principal in App::Group::"Security",
    action in [App::Action::"ViewFile", App::Action::"DownloadFile"],
    resource is App::Document
)
when
{
    principal is App::User &&
    resource is App::Document &&
    principal.jobTitle like "*Security Engineer" &&
    resource.dataClassification == "Critical"
};
