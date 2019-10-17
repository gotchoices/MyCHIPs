#----------------------------------------------------------------

#Default role all regular users belong to
namespace eval mychips {
  set adminuser	{admin}
  set usergroup	{mychips}
}

#Structure gets parsed in wyselib to create permissioning role groups
namespace eval base {
  set priv_roles {
    mychips	{peer_2 contract_1 tally_2 mychips_1}
  }
}

#Examples for full ERP access might include:
#    sales	{cust_2}
#    account	{vend_2 ent_1 gl_2}
#    admin	{empl_3 ent_3 gl_1 priv_2}
#    hr		{gl_1 empl_2 payroll_2}
