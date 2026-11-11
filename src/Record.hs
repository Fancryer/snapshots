module Record(
    taMut,
    taName,
    taTypeArg,
    eMut,
    eName,
    eTyp,
    eExp
)
where
import Types (ERecordProp (ERecordProp), Mutability, Typ, Expr, TARecordProp (..), TypeArg)
import Data.Text (Text)

taMut :: TARecordProp -> Mutability
taMut (TARecordProp m _ _) = m

taName :: TARecordProp -> Text
taName (TARecordProp _ n _) = n

taTypeArg :: TARecordProp -> TypeArg
taTypeArg (TARecordProp _ _ t) = t

eMut :: ERecordProp -> Mutability
eMut (ERecordProp m _ _ _) = m

eName :: ERecordProp -> Text
eName (ERecordProp _ n _ _) = n

eTyp :: ERecordProp -> Maybe Typ
eTyp (ERecordProp _ _ t _) = t

eExp :: ERecordProp -> Expr
eExp (ERecordProp _ _ _ e) = e