x=""
names=["v_0","v_1","v_2","v_3","par1","par2","par3","wel","weq","wal","wex","wim","wa","wn","select"]
for(var i of names){
    eval(i+"=y=>x+='"+i+"(); '")
}