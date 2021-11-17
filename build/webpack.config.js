// webpack.config.js
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
const VueLoaderPlugin = require('vue-loader/lib/plugin')
const path = require('path');
                
module.exports = {
  entry: {
    admin:'./src/admin.js',
    user: './src/user.js',
    report: './src/report.js',
    contract: './src/contract.js',
  },
  output: {
    path: path.join(__dirname, '..', 'pub'),
    filename: '[name]-bundle.js'
  },
  resolve: {
    alias: {
      vue: 'vue/dist/vue.js'
    },
//    mainFields: ['main', 'module']
  },
  plugins: [
    new VueLoaderPlugin(),
  ],
  performance: {
    maxAssetSize: 2000000,
    maxEntrypointSize: 1000000
  },
  module: {
    rules: [
      {
        test: /\.js$/,
        exclude: /(node_modules|bower_components)/,
        use: {
          loader: 'babel-loader',
          options: {
            presets: ['@babel/preset-env']
          }
        }
      },
      {
        test: /\.vue$/,
        exclude: /(node_modules|bower_components)/,
        use: [ 'vue-loader' ]
      },
      {
        test: /\.(less|css)$/,
        use: [ 'style-loader', 'css-loader', 'less-loader' ],
      },
      {
        test: /\.scss$/,
        use: [ 'style-loader', 'css-loader', 'sass-loader' ],
      },
      {
        test: /.*\.(gif|png|jpe?g)$/i,
        use: [ 'file-loader' ],
      },
      {
        test: /.*\.svg$/i,
        use: [ 'file-loader?name=[path][name].[ext]&context=./lib' ],
      }
    ]
  },
  devServer: {
       port: 3000,
       host: '0.0.0.0', disableHostCheck: true,	//To browse from different host on lan
       hot: true, hotOnly: true,
       contentBase: 'pub'
   }
}
