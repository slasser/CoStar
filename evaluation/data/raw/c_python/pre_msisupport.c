# 1 "msisupport.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "msisupport.c"







static UINT debug(MSIHANDLE hInstall, LPCSTR msg)
{
    MSIHANDLE hRec = MsiCreateRecord(1);
    if (!hRec || MsiRecordSetStringA(hRec, 1, msg) != ERROR_SUCCESS) {
        return ERROR_INSTALL_FAILURE;
    }
    MsiProcessMessage(hInstall, INSTALLMESSAGE_INFO, hRec);
    MsiCloseHandle(hRec);
    return ERROR_SUCCESS;
}




UINT __declspec(dllexport) __stdcall CheckDir(MSIHANDLE hInstall)
{

    WCHAR wpath[1024];
    char path[1024];
    UINT result;
    DWORD size = 1024;
    DWORD attributes;


    result = MsiGetPropertyW(hInstall, L"TARGETDIR", wpath, &size);
    if (result != ERROR_SUCCESS)
        return result;
    wpath[size] = L'\0';
    path[size] = L'\0';

    attributes = GetFileAttributesW(wpath);
    if (attributes == INVALID_FILE_ATTRIBUTES ||
        !(attributes & FILE_ATTRIBUTE_DIRECTORY))
    {
        return MsiSetPropertyA(hInstall, "TargetExists", "0");
    } else {
        return MsiSetPropertyA(hInstall, "TargetExists", "1");
    }
}





UINT __declspec(dllexport) __stdcall UpdateEditIDLE(MSIHANDLE hInstall)
{
    INSTALLSTATE ext_old, ext_new, tcl_old, tcl_new, reg_new;
    UINT result;

    result = MsiGetFeatureStateA(hInstall, "Extensions", &ext_old, &ext_new);
    if (result != ERROR_SUCCESS)
        return result;
    result = MsiGetFeatureStateA(hInstall, "TclTk", &tcl_old, &tcl_new);
    if (result != ERROR_SUCCESS)
        return result;




    if (ext_new == INSTALLSTATE_UNKNOWN)
        ext_new = ext_old;
    if (tcl_new == INSTALLSTATE_UNKNOWN)
        tcl_new = tcl_old;


    if (((tcl_new == INSTALLSTATE_LOCAL) ||
             (tcl_new == INSTALLSTATE_SOURCE) ||
             (tcl_new == INSTALLSTATE_DEFAULT)) &&
        ((ext_new == INSTALLSTATE_LOCAL) ||
         (ext_new == INSTALLSTATE_SOURCE) ||
         (ext_new == INSTALLSTATE_DEFAULT))) {
        reg_new = INSTALLSTATE_SOURCE;
    } else {
        reg_new = INSTALLSTATE_ABSENT;
    }
    result = MsiSetComponentStateA(hInstall, "REGISTRY.tcl", reg_new);
    return result;
}

BOOL APIENTRY DllMain(HANDLE hModule,
                      DWORD ul_reason_for_call,
                      LPVOID lpReserved)
{
    return TRUE;
}
