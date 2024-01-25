{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -Wno-prepositive-qualified-module #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_math_lib (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath




bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/Users/giovannigravili/.cabal/bin"
libdir     = "/Users/giovannigravili/.cabal/lib/aarch64-osx-ghc-9.4.8/math-lib-0.1.0.0-inplace-math-lib"
dynlibdir  = "/Users/giovannigravili/.cabal/lib/aarch64-osx-ghc-9.4.8"
datadir    = "/Users/giovannigravili/.cabal/share/aarch64-osx-ghc-9.4.8/math-lib-0.1.0.0"
libexecdir = "/Users/giovannigravili/.cabal/libexec/aarch64-osx-ghc-9.4.8/math-lib-0.1.0.0"
sysconfdir = "/Users/giovannigravili/.cabal/etc"

getBinDir     = catchIO (getEnv "math_lib_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "math_lib_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "math_lib_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "math_lib_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "math_lib_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "math_lib_sysconfdir") (\_ -> return sysconfdir)



joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
