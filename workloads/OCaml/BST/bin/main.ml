open BST.TypeBasedGenerator

let tests = [
  test_prop_InsertValid;
  test_prop_DeleteValid;
  test_prop_UnionValid;
  test_prop_InsertPost;
  test_prop_DeletePost;
  test_prop_UnionPost;
  test_prop_InsertModel;
  test_prop_DeleteModel;
  test_prop_UnionModel;
  test_prop_InsertInsert;
  test_prop_InsertDelete;
  test_prop_InsertUnion;
  test_prop_DeleteInsert;
  test_prop_DeleteDelete;
  test_prop_DeleteUnion;
  test_prop_UnionDeleteInsert;
  test_prop_UnionUnionIdem;
  test_prop_UnionUnionAssoc
];;

QCheck_runner.run_tests tests;;