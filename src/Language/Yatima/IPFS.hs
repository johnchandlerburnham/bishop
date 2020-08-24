{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
module Language.Yatima.IPFS where

import           Data.Aeson
import           Data.Proxy
import           Network.HTTP.Client  (defaultManagerSettings, newManager)

import qualified Data.ByteString      as B
import qualified Data.ByteString.Lazy as BSL
import           Data.Text            (Text)
import qualified Data.Text            as T
import           Servant.API
import           Servant.Client
import           Servant.Types.SourceT
import qualified Servant.Client.Streaming as S

import           Codec.Serialise
import           Language.Yatima.Term

import           Network.IPFS.API

apiCommands :: Proxy ApiV0Commands
apiCommands = Proxy

commands :: Maybe Bool -> ClientM Value
commands = client apiCommands

dagPut :: BSL.ByteString -> Maybe Text -> Maybe Text -> Maybe Bool -> Maybe Text
       -> ClientM Value
dagPut = client (Proxy :: Proxy ApiV0DagPut)

testAnon :: Anon
testAnon = LamA Many I64A (VarA 0)

fromRight (Right a) = a

testAnon2 = AppA (RefA (fromRight $ cidFromBase "zDPWYqFCsqGkVshbHjzLrTpkropq1vUpQ6KsXDkVr3kfQh4VDfo5")) (WrdA 1)

dagPutAnon :: Maybe Bool -> Anon -> ClientM Value
dagPutAnon pin anon =
  dagPut (serialise anon) (Just "cbor") (Just "cbor") pin (Just "blake2b-256")

dagGet :: Text -> S.ClientM (SourceIO B.ByteString)
dagGet = S.client (Proxy :: Proxy ApiV0DagGet)

testDagGet = dagGet "bafy2bzacebsjqvki6zhoeue5sxjltrgiazzh3lfcwuhhqtcchte3meccq3hj4"

run :: IO ()
run = do
  manager' <- newManager defaultManagerSettings
  let env = mkClientEnv manager' (BaseUrl Http "localhost" 5001 "")
  res <- runClientM (dagPutAnon (Just True) testAnon) env
  case res of
    Left err -> putStrLn $ "Error: " ++ show err
    Right val -> print val

get :: IO ()
get = do
  manager' <- newManager defaultManagerSettings
  let env = mkClientEnv manager' (BaseUrl Http "localhost" 5001 "")
  S.withClientM testDagGet env $ \e -> case e of
    Left err -> putStrLn $ "Error: " ++ show err
    Right rs -> foreach fail print rs


