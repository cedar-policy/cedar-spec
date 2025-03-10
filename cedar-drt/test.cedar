forbid (
  principal == a::"?",
  action,
  resource == a::"?"
)
when
{
  true &&
  ((if
      ((if
          false
        then
          (if
             false
           then
             (if
                false
              then
                (if false then principal else principal)
              else
                (if false then principal else resource))
           else
             (if
                false
              then
                (if false then principal else principal)
              else
                (if true then principal else principal)))
        else
          principal) in principal)
    then
      principal
    else
      principal) == principal)
};
